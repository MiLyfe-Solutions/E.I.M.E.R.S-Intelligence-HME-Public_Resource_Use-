import V185TrunkScan23Chunk1151

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6823314 : List Nat := [3, 2, 3, 3, 1, 2, 2, 1, 2, 2, 2]
def baseStart_6823314 : Nat := 118140960795 + 6823314 * 2 ^ 59
def prefixEnd_6823314 : Nat := 4983230072969 + 3 ^ 40 * 6823314 * 2
def baseEnd_6823314 : Nat := 3503639738552421986295157

theorem tailTrace_6823314 : CollatzResearch.WordTrace tailWord_6823314 prefixEnd_6823314 3503639738552421986295157 := by
  unfold tailWord_6823314
  simp only [CollatzResearch.WordTrace]
  refine ⟨62216676700576545524927249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165911137868204121399805997 62216676700576545524927249)
  ·
    refine ⟨46662507525432409143695437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62216676700576545524927249 46662507525432409143695437)
    ·
      refine ⟨17498440322037153428885789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46662507525432409143695437 17498440322037153428885789)
      ·
        refine ⟨6561915120763932535832171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17498440322037153428885789 6561915120763932535832171)
        ·
          refine ⟨9842872681145898803748257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6561915120763932535832171 9842872681145898803748257)
          ·
            refine ⟨7382154510859424102811193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9842872681145898803748257 7382154510859424102811193)
            ·
              refine ⟨5536615883144568077108395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7382154510859424102811193 5536615883144568077108395)
              ·
                refine ⟨8304923824716852115662593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5536615883144568077108395 8304923824716852115662593)
                ·
                  refine ⟨6228692868537639086746945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8304923824716852115662593 6228692868537639086746945)
                  ·
                    refine ⟨4671519651403229315060209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6228692868537639086746945 4671519651403229315060209)
                    ·
                      refine ⟨3503639738552421986295157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4671519651403229315060209 3503639738552421986295157)
                      ·
                        rfl

theorem cell23_6823314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_6823314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823314 prefixEnd_6823314 := by exact prefixLift 6823314
  have htrace : WordTrace (prefixWord ++ tailWord_6823314) baseStart_6823314 baseEnd_6823314 := by
    simpa [prefixWord, tailWord_6823314, baseEnd_6823314] using wordTrace_append hprefix tailTrace_6823314
  have hstable : (prefixWord ++ tailWord_6823314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823314).length < 2 ^ (prefixWord ++ tailWord_6823314).sum := by decide
  have hdescent : baseEnd_6823314 < baseStart_6823314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823319 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 1, 6, 2]
def baseStart_6823319 : Nat := 118140960795 + 6823319 * 2 ^ 59
def prefixEnd_6823319 : Nat := 4983230072969 + 3 ^ 40 * 6823319 * 2
def baseEnd_6823319 : Nat := 3503642305955694466732633

theorem tailTrace_6823319 : CollatzResearch.WordTrace tailWord_6823319 prefixEnd_6823319 3503642305955694466732633 := by
  unfold tailWord_6823319
  simp only [CollatzResearch.WordTrace]
  refine ⟨248866889167288067953641011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165911259444858711969094007 248866889167288067953641011)
  ·
    refine ⟨373300333750932101930461517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248866889167288067953641011 373300333750932101930461517)
    ·
      refine ⟨139987625156599538223923069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373300333750932101930461517 139987625156599538223923069)
      ·
        refine ⟨52495359433724826833971151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139987625156599538223923069 52495359433724826833971151)
        ·
          refine ⟨78743039150587240250956727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52495359433724826833971151 78743039150587240250956727)
          ·
            refine ⟨118114558725880860376435091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78743039150587240250956727 118114558725880860376435091)
            ·
              refine ⟨177171838088821290564652637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118114558725880860376435091 177171838088821290564652637)
              ·
                refine ⟨66439439283307983961744739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177171838088821290564652637 66439439283307983961744739)
                ·
                  refine ⟨99659158924961975942617109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66439439283307983961744739 99659158924961975942617109)
                  ·
                    refine ⟨4671523074607592622310177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 99659158924961975942617109 4671523074607592622310177)
                    ·
                      refine ⟨3503642305955694466732633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4671523074607592622310177 3503642305955694466732633)
                      ·
                        rfl

theorem cell23_6823319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_6823319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823319 prefixEnd_6823319 := by exact prefixLift 6823319
  have htrace : WordTrace (prefixWord ++ tailWord_6823319) baseStart_6823319 baseEnd_6823319 := by
    simpa [prefixWord, tailWord_6823319, baseEnd_6823319] using wordTrace_append hprefix tailTrace_6823319
  have hstable : (prefixWord ++ tailWord_6823319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823319).length < 2 ^ (prefixWord ++ tailWord_6823319).sum := by decide
  have hdescent : baseEnd_6823319 < baseStart_6823319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823332 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 1, 3, 6]
def baseStart_6823332 : Nat := 118140960795 + 6823332 * 2 ^ 59
def prefixEnd_6823332 : Nat := 4983230072969 + 3 ^ 40 * 6823332 * 2
def baseEnd_6823332 : Nat := 3503648981204202915870073

theorem tailTrace_6823332 : CollatzResearch.WordTrace tailWord_6823332 prefixEnd_6823332 3503648981204202915870073 := by
  unfold tailWord_6823332
  simp only [CollatzResearch.WordTrace]
  refine ⟨124433681658120485586932125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165911575544160647449242833 124433681658120485586932125)
  ·
    refine ⟨46662630621795182095099547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124433681658120485586932125 46662630621795182095099547)
    ·
      refine ⟨69993945932692773142649321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46662630621795182095099547 69993945932692773142649321)
      ·
        refine ⟨52495459449519579856986991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69993945932692773142649321 52495459449519579856986991)
        ·
          refine ⟨78743189174279369785480487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52495459449519579856986991 78743189174279369785480487)
          ·
            refine ⟨118114783761419054678220731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78743189174279369785480487 118114783761419054678220731)
            ·
              refine ⟨177172175642128582017331097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118114783761419054678220731 177172175642128582017331097)
              ·
                refine ⟨132879131731596436512998323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177172175642128582017331097 132879131731596436512998323)
                ·
                  refine ⟨199318697597394654769497485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132879131731596436512998323 199318697597394654769497485)
                  ·
                    refine ⟨74744511599022995538561557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 199318697597394654769497485 74744511599022995538561557)
                    ·
                      refine ⟨3503648981204202915870073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74744511599022995538561557 3503648981204202915870073)
                      ·
                        rfl

theorem cell23_6823332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_6823332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823332 prefixEnd_6823332 := by exact prefixLift 6823332
  have htrace : WordTrace (prefixWord ++ tailWord_6823332) baseStart_6823332 baseEnd_6823332 := by
    simpa [prefixWord, tailWord_6823332, baseEnd_6823332] using wordTrace_append hprefix tailTrace_6823332
  have hstable : (prefixWord ++ tailWord_6823332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823332).length < 2 ^ (prefixWord ++ tailWord_6823332).sum := by decide
  have hdescent : baseEnd_6823332 < baseStart_6823332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823363 : List Nat := [1, 1, 1, 3, 1, 1, 8, 2, 1, 4]
def baseStart_6823363 : Nat := 118140960795 + 6823363 * 2 ^ 59
def prefixEnd_6823363 : Nat := 4983230072969 + 3 ^ 40 * 6823363 * 2
def baseEnd_6823363 : Nat := 1167888299701497431527477

theorem tailTrace_6823363 : CollatzResearch.WordTrace tailWord_6823363 prefixEnd_6823363 1167888299701497431527477 := by
  unfold tailWord_6823363
  simp only [CollatzResearch.WordTrace]
  refine ⟨248868493979128663468242743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165912329319419108978828495 248868493979128663468242743)
  ·
    refine ⟨373302740968692995202364115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248868493979128663468242743 373302740968692995202364115)
    ·
      refine ⟨559954111453039492803546173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373302740968692995202364115 559954111453039492803546173)
      ·
        refine ⟨209982791794889809801329815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 559954111453039492803546173 209982791794889809801329815)
        ·
          refine ⟨314974187692334714701994723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209982791794889809801329815 314974187692334714701994723)
          ·
            refine ⟨472461281538502072052992085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314974187692334714701994723 472461281538502072052992085)
            ·
              refine ⟨5536655643029321156871001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 472461281538502072052992085 5536655643029321156871001)
              ·
                refine ⟨4152491732271990867653251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5536655643029321156871001 4152491732271990867653251)
                ·
                  refine ⟨6228737598407986301479877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4152491732271990867653251 6228737598407986301479877)
                  ·
                    refine ⟨1167888299701497431527477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6228737598407986301479877 1167888299701497431527477)
                    ·
                      rfl

theorem cell23_6823363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 2, 1, 4].length) (baseStart_6823363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823363 prefixEnd_6823363 := by exact prefixLift 6823363
  have htrace : WordTrace (prefixWord ++ tailWord_6823363) baseStart_6823363 baseEnd_6823363 := by
    simpa [prefixWord, tailWord_6823363, baseEnd_6823363] using wordTrace_append hprefix tailTrace_6823363
  have hstable : (prefixWord ++ tailWord_6823363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823363).length < 2 ^ (prefixWord ++ tailWord_6823363).sum := by decide
  have hdescent : baseEnd_6823363 < baseStart_6823363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823386 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 5, 1, 3]
def baseStart_6823386 : Nat := 118140960795 + 6823386 * 2 ^ 59
def prefixEnd_6823386 : Nat := 4983230072969 + 3 ^ 40 * 6823386 * 2
def baseEnd_6823386 : Nat := 3503676709159545704594825

theorem tailTrace_6823386 : CollatzResearch.WordTrace tailWord_6823386 prefixEnd_6823386 3503676709159545704594825 := by
  unfold tailWord_6823386
  simp only [CollatzResearch.WordTrace]
  refine ⟨62217333214511334599082503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165912888572030225597553341 62217333214511334599082503)
  ·
    refine ⟨93325999821767001898623755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62217333214511334599082503 93325999821767001898623755)
    ·
      refine ⟨139988999732650502847935633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93325999821767001898623755 139988999732650502847935633)
      ·
        refine ⟨104991749799487877135951725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139988999732650502847935633 104991749799487877135951725)
        ·
          refine ⟨39371906174807953925981897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104991749799487877135951725 39371906174807953925981897)
          ·
            refine ⟨29528929631105965444486423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39371906174807953925981897 29528929631105965444486423)
            ·
              refine ⟨44293394446658948166729635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29528929631105965444486423 44293394446658948166729635)
              ·
                refine ⟨66440091669988422250094453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44293394446658948166729635 66440091669988422250094453)
                ·
                  refine ⟨6228758594061414585946355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66440091669988422250094453 6228758594061414585946355)
                  ·
                    refine ⟨9343137891092121878919533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6228758594061414585946355 9343137891092121878919533)
                    ·
                      refine ⟨3503676709159545704594825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9343137891092121878919533 3503676709159545704594825)
                      ·
                        rfl

theorem cell23_6823386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_6823386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823386 prefixEnd_6823386 := by exact prefixLift 6823386
  have htrace : WordTrace (prefixWord ++ tailWord_6823386) baseStart_6823386 baseEnd_6823386 := by
    simpa [prefixWord, tailWord_6823386, baseEnd_6823386] using wordTrace_append hprefix tailTrace_6823386
  have hstable : (prefixWord ++ tailWord_6823386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823386).length < 2 ^ (prefixWord ++ tailWord_6823386).sum := by decide
  have hdescent : baseEnd_6823386 < baseStart_6823386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823406 : List Nat := [4, 1, 2, 1, 2, 1, 3, 3, 1, 5]
def baseStart_6823406 : Nat := 118140960795 + 6823406 * 2 ^ 59
def prefixEnd_6823406 : Nat := 4983230072969 + 3 ^ 40 * 6823406 * 2
def baseEnd_6823406 : Nat := 1167895659590878542114911

theorem tailTrace_6823406 : CollatzResearch.WordTrace tailWord_6823406 prefixEnd_6823406 1167895659590878542114911 := by
  unfold tailWord_6823406
  simp only [CollatzResearch.WordTrace]
  refine ⟨31108757789746610226507259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165913374878648587874705381 31108757789746610226507259)
  ·
    refine ⟨46663136684619915339760889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31108757789746610226507259 46663136684619915339760889)
    ·
      refine ⟨34997352513464936504820667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46663136684619915339760889 34997352513464936504820667)
      ·
        refine ⟨52496028770197404757231001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34997352513464936504820667 52496028770197404757231001)
        ·
          refine ⟨39372021577648053567923251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52496028770197404757231001 39372021577648053567923251)
          ·
            refine ⟨59058032366472080351884877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39372021577648053567923251 59058032366472080351884877)
            ·
              refine ⟨22146762137427030131956829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59058032366472080351884877 22146762137427030131956829)
              ·
                refine ⟨8305035801535136299483811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22146762137427030131956829 8305035801535136299483811)
                ·
                  refine ⟨12457553702302704449225717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8305035801535136299483811 12457553702302704449225717)
                  ·
                    refine ⟨1167895659590878542114911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12457553702302704449225717 1167895659590878542114911)
                    ·
                      rfl

theorem cell23_6823406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_6823406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823406 prefixEnd_6823406 := by exact prefixLift 6823406
  have htrace : WordTrace (prefixWord ++ tailWord_6823406) baseStart_6823406 baseEnd_6823406 := by
    simpa [prefixWord, tailWord_6823406, baseEnd_6823406] using wordTrace_append hprefix tailTrace_6823406
  have hstable : (prefixWord ++ tailWord_6823406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823406).length < 2 ^ (prefixWord ++ tailWord_6823406).sum := by decide
  have hdescent : baseEnd_6823406 < baseStart_6823406 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823419 : List Nat := [1, 1, 1, 1, 1, 3, 2, 5, 4, 4]
def baseStart_6823419 : Nat := 118140960795 + 6823419 * 2 ^ 59
def prefixEnd_6823419 : Nat := 4983230072969 + 3 ^ 40 * 6823419 * 2
def baseEnd_6823419 : Nat := 1167897884673714691827391

theorem tailTrace_6823419 : CollatzResearch.WordTrace tailWord_6823419 prefixEnd_6823419 1167897884673714691827391 := by
  unfold tailWord_6823419
  simp only [CollatzResearch.WordTrace]
  refine ⟨248870536466925785032281311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165913690977950523354854207 248870536466925785032281311)
  ·
    refine ⟨373305804700388677548421967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248870536466925785032281311 373305804700388677548421967)
    ·
      refine ⟨559958707050583016322632951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373305804700388677548421967 559958707050583016322632951)
      ·
        refine ⟨839938060575874524483949427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559958707050583016322632951 839938060575874524483949427)
        ·
          refine ⟨1259907090863811786725924141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 839938060575874524483949427 1259907090863811786725924141)
          ·
            refine ⟨472465159073929420022221553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1259907090863811786725924141 472465159073929420022221553)
            ·
              refine ⟨354348869305447065016666165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472465159073929420022221553 354348869305447065016666165)
              ·
                refine ⟨33220206497385662345312453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 354348869305447065016666165 33220206497385662345312453)
                ·
                  refine ⟨6228788718259811689746085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33220206497385662345312453 6228788718259811689746085)
                  ·
                    refine ⟨1167897884673714691827391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6228788718259811689746085 1167897884673714691827391)
                    ·
                      rfl

theorem cell23_6823419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 4, 4].length) (baseStart_6823419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823419 prefixEnd_6823419 := by exact prefixLift 6823419
  have htrace : WordTrace (prefixWord ++ tailWord_6823419) baseStart_6823419 baseEnd_6823419 := by
    simpa [prefixWord, tailWord_6823419, baseEnd_6823419] using wordTrace_append hprefix tailTrace_6823419
  have hstable : (prefixWord ++ tailWord_6823419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823419).length < 2 ^ (prefixWord ++ tailWord_6823419).sum := by decide
  have hdescent : baseEnd_6823419 < baseStart_6823419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823443 : List Nat := [1, 1, 1, 2, 1, 6, 2, 2, 3, 2, 2]
def baseStart_6823443 : Nat := 118140960795 + 6823443 * 2 ^ 59
def prefixEnd_6823443 : Nat := 4983230072969 + 3 ^ 40 * 6823443 * 2
def baseEnd_6823443 : Nat := 3503705977556851981582063

theorem tailTrace_6823443 : CollatzResearch.WordTrace tailWord_6823443 prefixEnd_6823443 3503705977556851981582063 := by
  unfold tailWord_6823443
  simp only [CollatzResearch.WordTrace]
  refine ⟨248871411818838837131154983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165914274545892558087436655 248871411818838837131154983)
  ·
    refine ⟨373307117728258255696732475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248871411818838837131154983 373307117728258255696732475)
    ·
      refine ⟨559960676592387383545098713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373307117728258255696732475 559960676592387383545098713)
      ·
        refine ⟨419970507444290537658824035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 559960676592387383545098713 419970507444290537658824035)
        ·
          refine ⟨629955761166435806488236053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419970507444290537658824035 629955761166435806488236053)
          ·
            refine ⟨29529176304676678429136065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 629955761166435806488236053 29529176304676678429136065)
            ·
              refine ⟨22146882228507508821852049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29529176304676678429136065 22146882228507508821852049)
              ·
                refine ⟨16610161671380631616389037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22146882228507508821852049 16610161671380631616389037)
                ·
                  refine ⟨6228810626767736856145889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16610161671380631616389037 6228810626767736856145889)
                  ·
                    refine ⟨4671607970075802642109417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6228810626767736856145889 4671607970075802642109417)
                    ·
                      refine ⟨3503705977556851981582063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4671607970075802642109417 3503705977556851981582063)
                      ·
                        rfl

theorem cell23_6823443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 3, 2, 2].length) (baseStart_6823443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823443 prefixEnd_6823443 := by exact prefixLift 6823443
  have htrace : WordTrace (prefixWord ++ tailWord_6823443) baseStart_6823443 baseEnd_6823443 := by
    simpa [prefixWord, tailWord_6823443, baseEnd_6823443] using wordTrace_append hprefix tailTrace_6823443
  have hstable : (prefixWord ++ tailWord_6823443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823443).length < 2 ^ (prefixWord ++ tailWord_6823443).sum := by decide
  have hdescent : baseEnd_6823443 < baseStart_6823443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823493 : List Nat := [1, 3, 1, 1, 1, 4, 3, 3, 2, 1, 3]
def baseStart_6823493 : Nat := 118140960795 + 6823493 * 2 ^ 59
def prefixEnd_6823493 : Nat := 4983230072969 + 3 ^ 40 * 6823493 * 2
def baseEnd_6823493 : Nat := 3503731651589576785956833

theorem tailTrace_6823493 : CollatzResearch.WordTrace tailWord_6823493 prefixEnd_6823493 3503731651589576785956833 := by
  unfold tailWord_6823493
  simp only [CollatzResearch.WordTrace]
  refine ⟨248873235468657695670475133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165915490312438463780316755 248873235468657695670475133)
  ·
    refine ⟨93327463300746635876428175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248873235468657695670475133 93327463300746635876428175)
    ·
      refine ⟨139991194951119953814642263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93327463300746635876428175 139991194951119953814642263)
      ·
        refine ⟨209986792426679930721963395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139991194951119953814642263 209986792426679930721963395)
        ·
          refine ⟨314980188640019896082945093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209986792426679930721963395 314980188640019896082945093)
          ·
            refine ⟨59058785370003730515552205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 314980188640019896082945093 59058785370003730515552205)
            ·
              refine ⟨22147044513751398943332077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59058785370003730515552205 22147044513751398943332077)
              ·
                refine ⟨8305141692656774603749529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22147044513751398943332077 8305141692656774603749529)
                ·
                  refine ⟨6228856269492580952812147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8305141692656774603749529 6228856269492580952812147)
                  ·
                    refine ⟨9343284404238871429218221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6228856269492580952812147 9343284404238871429218221)
                    ·
                      refine ⟨3503731651589576785956833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9343284404238871429218221 3503731651589576785956833)
                      ·
                        rfl

theorem cell23_6823493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 2, 1, 3].length) (baseStart_6823493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823493 prefixEnd_6823493 := by exact prefixLift 6823493
  have htrace : WordTrace (prefixWord ++ tailWord_6823493) baseStart_6823493 baseEnd_6823493 := by
    simpa [prefixWord, tailWord_6823493, baseEnd_6823493] using wordTrace_append hprefix tailTrace_6823493
  have hstable : (prefixWord ++ tailWord_6823493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823493).length < 2 ^ (prefixWord ++ tailWord_6823493).sum := by decide
  have hdescent : baseEnd_6823493 < baseStart_6823493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823494 : List Nat := [6, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4]
def baseStart_6823494 : Nat := 118140960795 + 6823494 * 2 ^ 59
def prefixEnd_6823494 : Nat := 4983230072969 + 3 ^ 40 * 6823494 * 2
def baseEnd_6823494 : Nat := 3503732165070231282044329

theorem tailTrace_6823494 : CollatzResearch.WordTrace tailWord_6823494 prefixEnd_6823494 3503732165070231282044329 := by
  unfold tailWord_6823494
  simp only [CollatzResearch.WordTrace]
  refine ⟨7777289748176689776289423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 165915514627769381894174357 7777289748176689776289423)
  ·
    refine ⟨11665934622265034664434135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7777289748176689776289423 11665934622265034664434135)
    ·
      refine ⟨17498901933397551996651203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11665934622265034664434135 17498901933397551996651203)
      ·
        refine ⟨26248352900096327994976805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17498901933397551996651203 26248352900096327994976805)
        ·
          refine ⟨4921566168768061499058151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26248352900096327994976805 4921566168768061499058151)
          ·
            refine ⟨7382349253152092248587227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4921566168768061499058151 7382349253152092248587227)
            ·
              refine ⟨11073523879728138372880841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7382349253152092248587227 11073523879728138372880841)
              ·
                refine ⟨8305142909796103779660631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11073523879728138372880841 8305142909796103779660631)
                ·
                  refine ⟨12457714364694155669490947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8305142909796103779660631 12457714364694155669490947)
                  ·
                    refine ⟨18686571547041233504236421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12457714364694155669490947 18686571547041233504236421)
                    ·
                      refine ⟨3503732165070231282044329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18686571547041233504236421 3503732165070231282044329)
                      ·
                        rfl

theorem cell23_6823494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_6823494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823494 prefixEnd_6823494 := by exact prefixLift 6823494
  have htrace : WordTrace (prefixWord ++ tailWord_6823494) baseStart_6823494 baseEnd_6823494 := by
    simpa [prefixWord, tailWord_6823494, baseEnd_6823494] using wordTrace_append hprefix tailTrace_6823494
  have hstable : (prefixWord ++ tailWord_6823494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823494).length < 2 ^ (prefixWord ++ tailWord_6823494).sum := by decide
  have hdescent : baseEnd_6823494 < baseStart_6823494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823509 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 4, 6]
def baseStart_6823509 : Nat := 118140960795 + 6823509 * 2 ^ 59
def prefixEnd_6823509 : Nat := 4983230072969 + 3 ^ 40 * 6823509 * 2
def baseEnd_6823509 : Nat := 1167913289093349574452253

theorem tailTrace_6823509 : CollatzResearch.WordTrace tailWord_6823509 prefixEnd_6823509 1167913289093349574452253 := by
  unfold tailWord_6823509
  simp only [CollatzResearch.WordTrace]
  refine ⟨248873819036599730403057581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165915879357733153602038387 248873819036599730403057581)
  ·
    refine ⟨93327682138724898901146593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248873819036599730403057581 93327682138724898901146593)
    ·
      refine ⟨69995761604043674175859945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93327682138724898901146593 69995761604043674175859945)
      ·
        refine ⟨52496821203032755631894959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69995761604043674175859945 52496821203032755631894959)
        ·
          refine ⟨78745231804549133447842439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52496821203032755631894959 78745231804549133447842439)
          ·
            refine ⟨118117847706823700171763659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78745231804549133447842439 118117847706823700171763659)
            ·
              refine ⟨177176771560235550257645489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118117847706823700171763659 177176771560235550257645489)
              ·
                refine ⟨132882578670176662693234117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177176771560235550257645489 132882578670176662693234117)
                ·
                  refine ⟨24915483500658124254981397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132882578670176662693234117 24915483500658124254981397)
                  ·
                    refine ⟨1167913289093349574452253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24915483500658124254981397 1167913289093349574452253)
                    ·
                      rfl

theorem cell23_6823509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_6823509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823509 prefixEnd_6823509 := by exact prefixLift 6823509
  have htrace : WordTrace (prefixWord ++ tailWord_6823509) baseStart_6823509 baseEnd_6823509 := by
    simpa [prefixWord, tailWord_6823509, baseEnd_6823509] using wordTrace_append hprefix tailTrace_6823509
  have hstable : (prefixWord ++ tailWord_6823509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823509).length < 2 ^ (prefixWord ++ tailWord_6823509).sum := by decide
  have hdescent : baseEnd_6823509 < baseStart_6823509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823536 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 3]
def baseStart_6823536 : Nat := 118140960795 + 6823536 * 2 ^ 59
def prefixEnd_6823536 : Nat := 4983230072969 + 3 ^ 40 * 6823536 * 2
def baseEnd_6823536 : Nat := 3503753731257720117719135

theorem tailTrace_6823536 : CollatzResearch.WordTrace tailWord_6823536 prefixEnd_6823536 3503753731257720117719135 := by
  unfold tailWord_6823536
  simp only [CollatzResearch.WordTrace]
  refine ⟨124437401903750957007145231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165916535871667942676193641 124437401903750957007145231)
  ·
    refine ⟨186656102855626435510717847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124437401903750957007145231 186656102855626435510717847)
    ·
      refine ⟨279984154283439653266076771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186656102855626435510717847 279984154283439653266076771)
      ·
        refine ⟨419976231425159479899115157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279984154283439653266076771 419976231425159479899115157)
        ·
          refine ⟨19686385848054350620271023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 419976231425159479899115157 19686385848054350620271023)
          ·
            refine ⟨29529578772081525930406535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19686385848054350620271023 29529578772081525930406535)
            ·
              refine ⟨44294368158122288895609803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29529578772081525930406535 44294368158122288895609803)
              ·
                refine ⟨66441552237183433343414705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44294368158122288895609803 66441552237183433343414705)
                ·
                  refine ⟨49831164177887575007561029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66441552237183433343414705 49831164177887575007561029)
                  ·
                    refine ⟨9343343283353920313917693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49831164177887575007561029 9343343283353920313917693)
                    ·
                      refine ⟨3503753731257720117719135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9343343283353920313917693 3503753731257720117719135)
                      ·
                        rfl

theorem cell23_6823536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 3].length) (baseStart_6823536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823536 prefixEnd_6823536 := by exact prefixLift 6823536
  have htrace : WordTrace (prefixWord ++ tailWord_6823536) baseStart_6823536 baseEnd_6823536 := by
    simpa [prefixWord, tailWord_6823536, baseEnd_6823536] using wordTrace_append hprefix tailTrace_6823536
  have hstable : (prefixWord ++ tailWord_6823536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823536).length < 2 ^ (prefixWord ++ tailWord_6823536).sum := by decide
  have hdescent : baseEnd_6823536 < baseStart_6823536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823683 : List Nat := [1, 1, 1, 3, 2, 2, 2, 3, 1, 5, 2]
def baseStart_6823683 : Nat := 118140960795 + 6823683 * 2 ^ 59
def prefixEnd_6823683 : Nat := 4983230072969 + 3 ^ 40 * 6823683 * 2
def baseEnd_6823683 : Nat := 3503829212913931042580959

theorem tailTrace_6823683 : CollatzResearch.WordTrace tailWord_6823683 prefixEnd_6823683 3503829212913931042580959 := by
  unfold tailWord_6823683
  simp only [CollatzResearch.WordTrace]
  refine ⟨248880165337969358119891703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165920110225312905413261135 248880165337969358119891703)
  ·
    refine ⟨373320248006954037179837555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248880165337969358119891703 373320248006954037179837555)
    ·
      refine ⟨559980372010431055769756333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373320248006954037179837555 559980372010431055769756333)
      ·
        refine ⟨209992639503911645913658625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 559980372010431055769756333 209992639503911645913658625)
        ·
          refine ⟨157494479627933734435243969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209992639503911645913658625 157494479627933734435243969)
          ·
            refine ⟨118120859720950300826432977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157494479627933734435243969 118120859720950300826432977)
            ·
              refine ⟨88590644790712725619824733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118120859720950300826432977 88590644790712725619824733)
              ·
                refine ⟨33221491796517272107434275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88590644790712725619824733 33221491796517272107434275)
                ·
                  refine ⟨49832237694775908161151413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33221491796517272107434275 49832237694775908161151413)
                  ·
                    refine ⟨4671772283885241390107945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49832237694775908161151413 4671772283885241390107945)
                    ·
                      refine ⟨3503829212913931042580959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4671772283885241390107945 3503829212913931042580959)
                      ·
                        rfl

theorem cell23_6823683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 5, 2].length) (baseStart_6823683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823683 prefixEnd_6823683 := by exact prefixLift 6823683
  have htrace : WordTrace (prefixWord ++ tailWord_6823683) baseStart_6823683 baseEnd_6823683 := by
    simpa [prefixWord, tailWord_6823683, baseEnd_6823683] using wordTrace_append hprefix tailTrace_6823683
  have hstable : (prefixWord ++ tailWord_6823683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823683).length < 2 ^ (prefixWord ++ tailWord_6823683).sum := by decide
  have hdescent : baseEnd_6823683 < baseStart_6823683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823713 : List Nat := [1, 2, 3, 2, 1, 3, 1, 2, 3, 1, 4]
def baseStart_6823713 : Nat := 118140960795 + 6823713 * 2 ^ 59
def prefixEnd_6823713 : Nat := 4983230072969 + 3 ^ 40 * 6823713 * 2
def baseEnd_6823713 : Nat := 3503844617333565925205821

theorem tailTrace_6823713 : CollatzResearch.WordTrace tailWord_6823713 prefixEnd_6823713 3503844617333565925205821 := by
  unfold tailWord_6823713
  simp only [CollatzResearch.WordTrace]
  refine ⟨248881259527860673243483793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165920839685240448828989195 248881259527860673243483793)
  ·
    refine ⟨186660944645895504932612845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248881259527860673243483793 186660944645895504932612845)
    ·
      refine ⟨69997854242210814349729817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186660944645895504932612845 69997854242210814349729817)
      ·
        refine ⟨52498390681658110762297363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69997854242210814349729817 52498390681658110762297363)
        ·
          refine ⟨78747586022487166143446045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52498390681658110762297363 78747586022487166143446045)
          ·
            refine ⟨29530344758432687303792267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78747586022487166143446045 29530344758432687303792267)
            ·
              refine ⟨44295517137649030955688401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29530344758432687303792267 44295517137649030955688401)
              ·
                refine ⟨33221637853236773216766301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44295517137649030955688401 33221637853236773216766301)
                ·
                  refine ⟨12458114194963789956287363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33221637853236773216766301 12458114194963789956287363)
                  ·
                    refine ⟨18687171292445684934431045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12458114194963789956287363 18687171292445684934431045)
                    ·
                      refine ⟨3503844617333565925205821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18687171292445684934431045 3503844617333565925205821)
                      ·
                        rfl

theorem cell23_6823713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_6823713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823713 prefixEnd_6823713 := by exact prefixLift 6823713
  have htrace : WordTrace (prefixWord ++ tailWord_6823713) baseStart_6823713 baseEnd_6823713 := by
    simpa [prefixWord, tailWord_6823713, baseEnd_6823713] using wordTrace_append hprefix tailTrace_6823713
  have hstable : (prefixWord ++ tailWord_6823713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823713).length < 2 ^ (prefixWord ++ tailWord_6823713).sum := by decide
  have hdescent : baseEnd_6823713 < baseStart_6823713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823734 : List Nat := [5, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2]
def baseStart_6823734 : Nat := 118140960795 + 6823734 * 2 ^ 59
def prefixEnd_6823734 : Nat := 4983230072969 + 3 ^ 40 * 6823734 * 2
def baseEnd_6823734 : Nat := 3503855400427310343043225

theorem tailTrace_6823734 : CollatzResearch.WordTrace tailWord_6823734 prefixEnd_6823734 3503855400427310343043225 := by
  unfold tailWord_6823734
  simp only [CollatzResearch.WordTrace]
  refine ⟨15555126591299037114374891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165921350307189729219998837 15555126591299037114374891)
  ·
    refine ⟨23332689886948555671562337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15555126591299037114374891 23332689886948555671562337)
    ·
      refine ⟨17499517415211416753671753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23332689886948555671562337 17499517415211416753671753)
      ·
        refine ⟨13124638061408562565253815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17499517415211416753671753 13124638061408562565253815)
        ·
          refine ⟨19686957092112843847880723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13124638061408562565253815 19686957092112843847880723)
          ·
            refine ⟨29530435638169265771821085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19686957092112843847880723 29530435638169265771821085)
            ·
              refine ⟨11073913364313474664432907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29530435638169265771821085 11073913364313474664432907)
              ·
                refine ⟨16610870046470211996649361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11073913364313474664432907 16610870046470211996649361)
                ·
                  refine ⟨12458152534852658997487021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16610870046470211996649361 12458152534852658997487021)
                  ·
                    refine ⟨4671807200569747124057633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12458152534852658997487021 4671807200569747124057633)
                    ·
                      refine ⟨3503855400427310343043225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4671807200569747124057633 3503855400427310343043225)
                      ·
                        rfl

theorem cell23_6823734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_6823734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823734 prefixEnd_6823734 := by exact prefixLift 6823734
  have htrace : WordTrace (prefixWord ++ tailWord_6823734) baseStart_6823734 baseEnd_6823734 := by
    simpa [prefixWord, tailWord_6823734, baseEnd_6823734] using wordTrace_append hprefix tailTrace_6823734
  have hstable : (prefixWord ++ tailWord_6823734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823734).length < 2 ^ (prefixWord ++ tailWord_6823734).sum := by decide
  have hdescent : baseEnd_6823734 < baseStart_6823734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823747 : List Nat := [1, 1, 1, 3, 1, 7, 2, 1, 1, 1, 4]
def baseStart_6823747 : Nat := 118140960795 + 6823747 * 2 ^ 59
def prefixEnd_6823747 : Nat := 4983230072969 + 3 ^ 40 * 6823747 * 2
def baseEnd_6823747 : Nat := 3503862075675818792180665

theorem tailTrace_6823747 : CollatzResearch.WordTrace tailWord_6823747 prefixEnd_6823747 3503862075675818792180665 := by
  unfold tailWord_6823747
  simp only [CollatzResearch.WordTrace]
  refine ⟨248882499609737497050221495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165921666406491664700147663 248882499609737497050221495)
  ·
    refine ⟨373323749414606245575332243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248882499609737497050221495 373323749414606245575332243)
    ·
      refine ⟨559985624121909368362998365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373323749414606245575332243 559985624121909368362998365)
      ·
        refine ⟨209994609045716013136124387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 559985624121909368362998365 209994609045716013136124387)
        ·
          refine ⟨314991913568574019704186581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209994609045716013136124387 314991913568574019704186581)
          ·
            refine ⟨7382622974263453586816873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 314991913568574019704186581 7382622974263453586816873)
            ·
              refine ⟨5536967230697590190112655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7382622974263453586816873 5536967230697590190112655)
              ·
                refine ⟨8305450846046385285168983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5536967230697590190112655 8305450846046385285168983)
                ·
                  refine ⟨12458176269069577927753475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8305450846046385285168983 12458176269069577927753475)
                  ·
                    refine ⟨18687264403604366891630213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12458176269069577927753475 18687264403604366891630213)
                    ·
                      refine ⟨3503862075675818792180665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18687264403604366891630213 3503862075675818792180665)
                      ·
                        rfl

theorem cell23_6823747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 1, 1, 4].length) (baseStart_6823747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823747 prefixEnd_6823747 := by exact prefixLift 6823747
  have htrace : WordTrace (prefixWord ++ tailWord_6823747) baseStart_6823747 baseEnd_6823747 := by
    simpa [prefixWord, tailWord_6823747, baseEnd_6823747] using wordTrace_append hprefix tailTrace_6823747
  have hstable : (prefixWord ++ tailWord_6823747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823747).length < 2 ^ (prefixWord ++ tailWord_6823747).sum := by decide
  have hdescent : baseEnd_6823747 < baseStart_6823747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823757 : List Nat := [1, 6, 1, 2, 1, 2, 1, 1, 4, 4]
def baseStart_6823757 : Nat := 118140960795 + 6823757 * 2 ^ 59
def prefixEnd_6823757 : Nat := 4983230072969 + 3 ^ 40 * 6823757 * 2
def baseEnd_6823757 : Nat := 1167955736827454584351873

theorem tailTrace_6823757 : CollatzResearch.WordTrace tailWord_6823757 prefixEnd_6823757 1167955736827454584351873 := by
  unfold tailWord_6823757
  simp only [CollatzResearch.WordTrace]
  refine ⟨248882864339701268758085525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165921909559800845838723683 248882864339701268758085525)
  ·
    refine ⟨11666384265923496973035259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 248882864339701268758085525 11666384265923496973035259)
    ·
      refine ⟨17499576398885245459552889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11666384265923496973035259 17499576398885245459552889)
      ·
        refine ⟨13124682299163934094664667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17499576398885245459552889 13124682299163934094664667)
        ·
          refine ⟨19687023448745901141997001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13124682299163934094664667 19687023448745901141997001)
          ·
            refine ⟨14765267586559425856497751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19687023448745901141997001 14765267586559425856497751)
            ·
              refine ⟨22147901379839138784746627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14765267586559425856497751 22147901379839138784746627)
              ·
                refine ⟨33221852069758708177119941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22147901379839138784746627 33221852069758708177119941)
                ·
                  refine ⟨6229097263079757783209989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33221852069758708177119941 6229097263079757783209989)
                  ·
                    refine ⟨1167955736827454584351873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6229097263079757783209989 1167955736827454584351873)
                    ·
                      rfl

theorem cell23_6823757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_6823757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823757 prefixEnd_6823757 := by exact prefixLift 6823757
  have htrace : WordTrace (prefixWord ++ tailWord_6823757) baseStart_6823757 baseEnd_6823757 := by
    simpa [prefixWord, tailWord_6823757, baseEnd_6823757] using wordTrace_append hprefix tailTrace_6823757
  have hstable : (prefixWord ++ tailWord_6823757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823757).length < 2 ^ (prefixWord ++ tailWord_6823757).sum := by decide
  have hdescent : baseEnd_6823757 < baseStart_6823757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823764 : List Nat := [2, 4, 1, 1, 3, 2, 2, 1, 3, 2, 2]
def baseStart_6823764 : Nat := 118140960795 + 6823764 * 2 ^ 59
def prefixEnd_6823764 : Nat := 4983230072969 + 3 ^ 40 * 6823764 * 2
def baseEnd_6823764 : Nat := 3503870804846945225668087

theorem tailTrace_6823764 : CollatzResearch.WordTrace tailWord_6823764 prefixEnd_6823764 3503870804846945225668087 := by
  unfold tailWord_6823764
  simp only [CollatzResearch.WordTrace]
  refine ⟨124441559825337954476795173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165922079767117272635726897 124441559825337954476795173)
  ·
    refine ⟨23332792467250866464399095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124441559825337954476795173 23332792467250866464399095)
    ·
      refine ⟨34999188700876299696598643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23332792467250866464399095 34999188700876299696598643)
      ·
        refine ⟨52498783051314449544897965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34999188700876299696598643 52498783051314449544897965)
        ·
          refine ⟨19687043644242918579336737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52498783051314449544897965 19687043644242918579336737)
          ·
            refine ⟨14765282733182188934502553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19687043644242918579336737 14765282733182188934502553)
            ·
              refine ⟨11073962049886641700876915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14765282733182188934502553 11073962049886641700876915)
              ·
                refine ⟨16610943074829962551315373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11073962049886641700876915 16610943074829962551315373)
                ·
                  refine ⟨6229103653061235956743265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16610943074829962551315373 6229103653061235956743265)
                  ·
                    refine ⟨4671827739795926967557449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6229103653061235956743265 4671827739795926967557449)
                    ·
                      refine ⟨3503870804846945225668087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4671827739795926967557449 3503870804846945225668087)
                      ·
                        rfl

theorem cell23_6823764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_6823764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823764 prefixEnd_6823764 := by exact prefixLift 6823764
  have htrace : WordTrace (prefixWord ++ tailWord_6823764) baseStart_6823764 baseEnd_6823764 := by
    simpa [prefixWord, tailWord_6823764, baseEnd_6823764] using wordTrace_append hprefix tailTrace_6823764
  have hstable : (prefixWord ++ tailWord_6823764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823764).length < 2 ^ (prefixWord ++ tailWord_6823764).sum := by decide
  have hdescent : baseEnd_6823764 < baseStart_6823764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823833 : List Nat := [1, 2, 1, 2, 1, 3, 2, 3, 2, 2, 4]
def baseStart_6823833 : Nat := 118140960795 + 6823833 * 2 ^ 59
def prefixEnd_6823833 : Nat := 4983230072969 + 3 ^ 40 * 6823833 * 2
def baseEnd_6823833 : Nat := 3503906235012105455705269

theorem tailTrace_6823833 : CollatzResearch.WordTrace tailWord_6823833 prefixEnd_6823833 3503906235012105455705269 := by
  unfold tailWord_6823833
  simp only [CollatzResearch.WordTrace]
  refine ⟨248885636287425933737852153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165923757524950622491901435 248885636287425933737852153)
  ·
    refine ⟨186664227215569450303389115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248885636287425933737852153 186664227215569450303389115)
    ·
      refine ⟨279996340823354175455083673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186664227215569450303389115 279996340823354175455083673)
      ·
        refine ⟨209997255617515631591312755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279996340823354175455083673 209997255617515631591312755)
        ·
          refine ⟨314995883426273447386969133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209997255617515631591312755 314995883426273447386969133)
          ·
            refine ⟨118123456284852542770113425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 314995883426273447386969133 118123456284852542770113425)
            ·
              refine ⟨88592592213639407077585069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118123456284852542770113425 88592592213639407077585069)
              ·
                refine ⟨33222222080114777654094401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88592592213639407077585069 33222222080114777654094401)
                ·
                  refine ⟨24916666560086083240570801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33222222080114777654094401 24916666560086083240570801)
                  ·
                    refine ⟨18687499920064562430428101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24916666560086083240570801 18687499920064562430428101)
                    ·
                      refine ⟨3503906235012105455705269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18687499920064562430428101 3503906235012105455705269)
                      ·
                        rfl

theorem cell23_6823833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_6823833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823833 prefixEnd_6823833 := by exact prefixLift 6823833
  have htrace : WordTrace (prefixWord ++ tailWord_6823833) baseStart_6823833 baseEnd_6823833 := by
    simpa [prefixWord, tailWord_6823833, baseEnd_6823833] using wordTrace_append hprefix tailTrace_6823833
  have hstable : (prefixWord ++ tailWord_6823833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823833).length < 2 ^ (prefixWord ++ tailWord_6823833).sum := by decide
  have hdescent : baseEnd_6823833 < baseStart_6823833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823841 : List Nat := [1, 2, 3, 4, 2, 2, 1, 2, 1, 3, 2]
def baseStart_6823841 : Nat := 118140960795 + 6823841 * 2 ^ 59
def prefixEnd_6823841 : Nat := 4983230072969 + 3 ^ 40 * 6823841 * 2
def baseEnd_6823841 : Nat := 3503910342857341424405233

theorem tailTrace_6823841 : CollatzResearch.WordTrace tailWord_6823841 prefixEnd_6823841 3503910342857341424405233 := by
  unfold tailWord_6823841
  simp only [CollatzResearch.WordTrace]
  refine ⟨248885928071396951104143377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165923952047597967402762251 248885928071396951104143377)
  ·
    refine ⟨186664446053547713328107533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248885928071396951104143377 186664446053547713328107533)
    ·
      refine ⟨69999167270080392498040325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186664446053547713328107533 69999167270080392498040325)
      ·
        refine ⟨13124843863140073593382561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69999167270080392498040325 13124843863140073593382561)
        ·
          refine ⟨9843632897355055195036921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13124843863140073593382561 9843632897355055195036921)
          ·
            refine ⟨7382724673016291396277691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9843632897355055195036921 7382724673016291396277691)
            ·
              refine ⟨11074087009524437094416537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7382724673016291396277691 11074087009524437094416537)
              ·
                refine ⟨8305565257143327820812403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11074087009524437094416537 8305565257143327820812403)
                ·
                  refine ⟨12458347885714991731218605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8305565257143327820812403 12458347885714991731218605)
                  ·
                    refine ⟨4671880457143121899206977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12458347885714991731218605 4671880457143121899206977)
                    ·
                      refine ⟨3503910342857341424405233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4671880457143121899206977 3503910342857341424405233)
                      ·
                        rfl

theorem cell23_6823841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_6823841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823841 prefixEnd_6823841 := by exact prefixLift 6823841
  have htrace : WordTrace (prefixWord ++ tailWord_6823841) baseStart_6823841 baseEnd_6823841 := by
    simpa [prefixWord, tailWord_6823841, baseEnd_6823841] using wordTrace_append hprefix tailTrace_6823841
  have hstable : (prefixWord ++ tailWord_6823841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823841).length < 2 ^ (prefixWord ++ tailWord_6823841).sum := by decide
  have hdescent : baseEnd_6823841 < baseStart_6823841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823883 : List Nat := [1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 5]
def baseStart_6823883 : Nat := 118140960795 + 6823883 * 2 ^ 59
def prefixEnd_6823883 : Nat := 4983230072969 + 3 ^ 40 * 6823883 * 2
def baseEnd_6823883 : Nat := 3503931909044830260080039

theorem tailTrace_6823883 : CollatzResearch.WordTrace tailWord_6823883 prefixEnd_6823883 3503931909044830260080039 := by
  unfold tailWord_6823883
  simp only [CollatzResearch.WordTrace]
  refine ⟨248887459937244792277172303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165924973291496528184781535 248887459937244792277172303)
  ·
    refine ⟨373331189905867188415758455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248887459937244792277172303 373331189905867188415758455)
    ·
      refine ⟨559996784858800782623637683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373331189905867188415758455 559996784858800782623637683)
      ·
        refine ⟨839995177288201173935456525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559996784858800782623637683 839995177288201173935456525)
        ·
          refine ⟨314998191483075440225796197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 839995177288201173935456525 314998191483075440225796197)
          ·
            refine ⟨59062160903076645042336787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 314998191483075440225796197 59062160903076645042336787)
            ·
              refine ⟨88593241354614967563505181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59062160903076645042336787 88593241354614967563505181)
              ·
                refine ⟨33222465507980612836314443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88593241354614967563505181 33222465507980612836314443)
                ·
                  refine ⟨49833698261970919254471665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33222465507980612836314443 49833698261970919254471665)
                  ·
                    refine ⟨37375273696478189440853749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49833698261970919254471665 37375273696478189440853749)
                    ·
                      refine ⟨3503931909044830260080039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37375273696478189440853749 3503931909044830260080039)
                      ·
                        rfl

theorem cell23_6823883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 5].length) (baseStart_6823883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823883 prefixEnd_6823883 := by exact prefixLift 6823883
  have htrace : WordTrace (prefixWord ++ tailWord_6823883) baseStart_6823883 baseEnd_6823883 := by
    simpa [prefixWord, tailWord_6823883, baseEnd_6823883] using wordTrace_append hprefix tailTrace_6823883
  have hstable : (prefixWord ++ tailWord_6823883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823883).length < 2 ^ (prefixWord ++ tailWord_6823883).sum := by decide
  have hdescent : baseEnd_6823883 < baseStart_6823883 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823907 : List Nat := [1, 1, 1, 6, 1, 4, 1, 1, 2, 5]
def baseStart_6823907 : Nat := 118140960795 + 6823907 * 2 ^ 59
def prefixEnd_6823907 : Nat := 4983230072969 + 3 ^ 40 * 6823907 * 2
def baseEnd_6823907 : Nat := 1167981410860179388726643

theorem tailTrace_6823907 : CollatzResearch.WordTrace tailWord_6823907 prefixEnd_6823907 1167981410860179388726643 := by
  unfold tailWord_6823907
  simp only [CollatzResearch.WordTrace]
  refine ⟨248888335289157844376045975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165925556859438562917363983 248888335289157844376045975)
  ·
    refine ⟨373332502933736766564068963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248888335289157844376045975 373332502933736766564068963)
    ·
      refine ⟨559998754400605149846103445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373332502933736766564068963 559998754400605149846103445)
      ·
        refine ⟨26249941612528366399036099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 559998754400605149846103445 26249941612528366399036099)
        ·
          refine ⟨39374912418792549598554149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26249941612528366399036099 39374912418792549598554149)
          ·
            refine ⟨7382796078523603049728903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39374912418792549598554149 7382796078523603049728903)
            ·
              refine ⟨11074194117785404574593355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7382796078523603049728903 11074194117785404574593355)
              ·
                refine ⟨16611291176678106861890033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11074194117785404574593355 16611291176678106861890033)
                ·
                  refine ⟨12458468382508580146417525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16611291176678106861890033 12458468382508580146417525)
                  ·
                    refine ⟨1167981410860179388726643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12458468382508580146417525 1167981410860179388726643)
                    ·
                      rfl

theorem cell23_6823907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 5].length) (baseStart_6823907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823907 prefixEnd_6823907 := by exact prefixLift 6823907
  have htrace : WordTrace (prefixWord ++ tailWord_6823907) baseStart_6823907 baseEnd_6823907 := by
    simpa [prefixWord, tailWord_6823907, baseEnd_6823907] using wordTrace_append hprefix tailTrace_6823907
  have hstable : (prefixWord ++ tailWord_6823907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823907).length < 2 ^ (prefixWord ++ tailWord_6823907).sum := by decide
  have hdescent : baseEnd_6823907 < baseStart_6823907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823923 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 4]
def baseStart_6823923 : Nat := 118140960795 + 6823923 * 2 ^ 59
def prefixEnd_6823923 : Nat := 4983230072969 + 3 ^ 40 * 6823923 * 2
def baseEnd_6823923 : Nat := 3503952448271010103579855

theorem tailTrace_6823923 : CollatzResearch.WordTrace tailWord_6823923 prefixEnd_6823923 3503952448271010103579855 := by
  unfold tailWord_6823923
  simp only [CollatzResearch.WordTrace]
  refine ⟨248888918857099879108628423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165925945904733252739085615 248888918857099879108628423)
  ·
    refine ⟨373333378285649818662942635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248888918857099879108628423 373333378285649818662942635)
    ·
      refine ⟨560000067428474727994413953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373333378285649818662942635 560000067428474727994413953)
      ·
        refine ⟨420000050571356045995810465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 560000067428474727994413953 420000050571356045995810465)
        ·
          refine ⟨315000037928517034496857849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420000050571356045995810465 315000037928517034496857849)
          ·
            refine ⟨236250028446387775872643387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315000037928517034496857849 236250028446387775872643387)
            ·
              refine ⟨354375042669581663808965081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236250028446387775872643387 354375042669581663808965081)
              ·
                refine ⟨265781282002186247856723811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354375042669581663808965081 265781282002186247856723811)
                ·
                  refine ⟨398671923003279371785085717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265781282002186247856723811 398671923003279371785085717)
                  ·
                    refine ⟨18687746390778720552425893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 398671923003279371785085717 18687746390778720552425893)
                    ·
                      refine ⟨3503952448271010103579855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18687746390778720552425893 3503952448271010103579855)
                      ·
                        rfl

theorem cell23_6823923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 4].length) (baseStart_6823923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823923 prefixEnd_6823923 := by exact prefixLift 6823923
  have htrace : WordTrace (prefixWord ++ tailWord_6823923) baseStart_6823923 baseEnd_6823923 := by
    simpa [prefixWord, tailWord_6823923, baseEnd_6823923] using wordTrace_append hprefix tailTrace_6823923
  have hstable : (prefixWord ++ tailWord_6823923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823923).length < 2 ^ (prefixWord ++ tailWord_6823923).sum := by decide
  have hdescent : baseEnd_6823923 < baseStart_6823923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823937 : List Nat := [1, 2, 4, 1, 2, 1, 4, 1, 3, 4]
def baseStart_6823937 : Nat := 118140960795 + 6823937 * 2 ^ 59
def prefixEnd_6823937 : Nat := 4983230072969 + 3 ^ 40 * 6823937 * 2
def baseEnd_6823937 : Nat := 1167986545666724349601597

theorem tailTrace_6823937 : CollatzResearch.WordTrace tailWord_6823937 prefixEnd_6823937 1167986545666724349601597 := by
  unfold tailWord_6823937
  simp only [CollatzResearch.WordTrace]
  refine ⟨248889429479049159499638065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165926286319366106333092043 248889429479049159499638065)
  ·
    refine ⟨186667072109286869624728549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248889429479049159499638065 186667072109286869624728549)
    ·
      refine ⟨35000076020491288054636603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186667072109286869624728549 35000076020491288054636603)
      ·
        refine ⟨52500114030736932081954905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35000076020491288054636603 52500114030736932081954905)
        ·
          refine ⟨39375085523052699061466179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52500114030736932081954905 39375085523052699061466179)
          ·
            refine ⟨59062628284579048592199269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39375085523052699061466179 59062628284579048592199269)
            ·
              refine ⟨11074242803358571611037363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59062628284579048592199269 11074242803358571611037363)
              ·
                refine ⟨16611364205037857416556045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11074242803358571611037363 16611364205037857416556045)
                ·
                  refine ⟨6229261576889196531208517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16611364205037857416556045 6229261576889196531208517)
                  ·
                    refine ⟨1167986545666724349601597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6229261576889196531208517 1167986545666724349601597)
                    ·
                      rfl

theorem cell23_6823937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_6823937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823937 prefixEnd_6823937 := by exact prefixLift 6823937
  have htrace : WordTrace (prefixWord ++ tailWord_6823937) baseStart_6823937 baseEnd_6823937 := by
    simpa [prefixWord, tailWord_6823937, baseEnd_6823937] using wordTrace_append hprefix tailTrace_6823937
  have hstable : (prefixWord ++ tailWord_6823937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823937).length < 2 ^ (prefixWord ++ tailWord_6823937).sum := by decide
  have hdescent : baseEnd_6823937 < baseStart_6823937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823960 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 2, 5, 3]
def baseStart_6823960 : Nat := 118140960795 + 6823960 * 2 ^ 59
def prefixEnd_6823960 : Nat := 4983230072969 + 3 ^ 40 * 6823960 * 2
def baseEnd_6823960 : Nat := 3503971447055226458817185

theorem tailTrace_6823960 : CollatzResearch.WordTrace tailWord_6823960 prefixEnd_6823960 3503971447055226458817185 := by
  unfold tailWord_6823960
  simp only [CollatzResearch.WordTrace]
  refine ⟨124445134178982917213862667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165926845571977222951816889 124445134178982917213862667)
  ·
    refine ⟨186667701268474375820794001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124445134178982917213862667 186667701268474375820794001)
    ·
      refine ⟨140000775951355781865595501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186667701268474375820794001 140000775951355781865595501)
      ·
        refine ⟨52500290981758418199598313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140000775951355781865595501 52500290981758418199598313)
        ·
          refine ⟨39375218236318813649698735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52500290981758418199598313 39375218236318813649698735)
          ·
            refine ⟨59062827354478220474548103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39375218236318813649698735 59062827354478220474548103)
            ·
              refine ⟨88594241031717330711822155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59062827354478220474548103 88594241031717330711822155)
              ·
                refine ⟨132891361547575996067733233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88594241031717330711822155 132891361547575996067733233)
                ·
                  refine ⟨99668521160681997050799925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132891361547575996067733233 99668521160681997050799925)
                  ·
                    refine ⟨9343923858813937223512493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99668521160681997050799925 9343923858813937223512493)
                    ·
                      refine ⟨3503971447055226458817185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9343923858813937223512493 3503971447055226458817185)
                      ·
                        rfl

theorem cell23_6823960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_6823960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823960 prefixEnd_6823960 := by exact prefixLift 6823960
  have htrace : WordTrace (prefixWord ++ tailWord_6823960) baseStart_6823960 baseEnd_6823960 := by
    simpa [prefixWord, tailWord_6823960, baseEnd_6823960] using wordTrace_append hprefix tailTrace_6823960
  have hstable : (prefixWord ++ tailWord_6823960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823960).length < 2 ^ (prefixWord ++ tailWord_6823960).sum := by decide
  have hdescent : baseEnd_6823960 < baseStart_6823960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823987 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 4, 3, 2]
def baseStart_6823987 : Nat := 118140960795 + 6823987 * 2 ^ 59
def prefixEnd_6823987 : Nat := 4983230072969 + 3 ^ 40 * 6823987 * 2
def baseEnd_6823987 : Nat := 3503985311032897853179561

theorem tailTrace_6823987 : CollatzResearch.WordTrace tailWord_6823987 prefixEnd_6823987 3503985311032897853179561 := by
  unfold tailWord_6823987
  simp only [CollatzResearch.WordTrace]
  refine ⟨248891253128868018038958215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165927502085912012025972143 248891253128868018038958215)
  ·
    refine ⟨373336879693302027058437323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248891253128868018038958215 373336879693302027058437323)
    ·
      refine ⟨560005319539953040587655985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373336879693302027058437323 560005319539953040587655985)
      ·
        refine ⟨420003989654964780440741989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 560005319539953040587655985 420003989654964780440741989)
        ·
          refine ⟨78750748060305896332639123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 420003989654964780440741989 78750748060305896332639123)
          ·
            refine ⟨118126122090458844498958685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78750748060305896332639123 118126122090458844498958685)
            ·
              refine ⟨44297295783922066687109507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118126122090458844498958685 44297295783922066687109507)
              ·
                refine ⟨66445943675883100030664261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44297295783922066687109507 66445943675883100030664261)
                ·
                  refine ⟨12458614439228081255749549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66445943675883100030664261 12458614439228081255749549)
                  ·
                    refine ⟨4671980414710530470906081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12458614439228081255749549 4671980414710530470906081)
                    ·
                      refine ⟨3503985311032897853179561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4671980414710530470906081 3503985311032897853179561)
                      ·
                        rfl

theorem cell23_6823987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 3, 2].length) (baseStart_6823987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823987 prefixEnd_6823987 := by exact prefixLift 6823987
  have htrace : WordTrace (prefixWord ++ tailWord_6823987) baseStart_6823987 baseEnd_6823987 := by
    simpa [prefixWord, tailWord_6823987, baseEnd_6823987] using wordTrace_append hprefix tailTrace_6823987
  have hstable : (prefixWord ++ tailWord_6823987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823987).length < 2 ^ (prefixWord ++ tailWord_6823987).sum := by decide
  have hdescent : baseEnd_6823987 < baseStart_6823987 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6823988 : List Nat := [2, 5, 1, 2, 3, 1, 1, 1, 3, 4]
def baseStart_6823988 : Nat := 118140960795 + 6823988 * 2 ^ 59
def prefixEnd_6823988 : Nat := 4983230072969 + 3 ^ 40 * 6823988 * 2
def baseEnd_6823988 : Nat := 1167995274837850783089019

theorem tailTrace_6823988 : CollatzResearch.WordTrace tailWord_6823988 prefixEnd_6823988 1167995274837850783089019 := by
  unfold tailWord_6823988
  simp only [CollatzResearch.WordTrace]
  refine ⟨124445644800932197604872309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165927526401242930139829745 124445644800932197604872309)
  ·
    refine ⟨11666779200087393525456779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124445644800932197604872309 11666779200087393525456779)
    ·
      refine ⟨17500168800131090288185169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11666779200087393525456779 17500168800131090288185169)
      ·
        refine ⟨13125126600098317716138877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17500168800131090288185169 13125126600098317716138877)
        ·
          refine ⟨4921922475036869143552079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13125126600098317716138877 4921922475036869143552079)
          ·
            refine ⟨7382883712555303715328119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4921922475036869143552079 7382883712555303715328119)
            ·
              refine ⟨11074325568832955572992179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7382883712555303715328119 11074325568832955572992179)
              ·
                refine ⟨16611488353249433359488269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11074325568832955572992179 16611488353249433359488269)
                ·
                  refine ⟨6229308132468537509808101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16611488353249433359488269 6229308132468537509808101)
                  ·
                    refine ⟨1167995274837850783089019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6229308132468537509808101 1167995274837850783089019)
                    ·
                      rfl

theorem cell23_6823988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_6823988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6823988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6823988 prefixEnd_6823988 := by exact prefixLift 6823988
  have htrace : WordTrace (prefixWord ++ tailWord_6823988) baseStart_6823988 baseEnd_6823988 := by
    simpa [prefixWord, tailWord_6823988, baseEnd_6823988] using wordTrace_append hprefix tailTrace_6823988
  have hstable : (prefixWord ++ tailWord_6823988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6823988).length < 2 ^ (prefixWord ++ tailWord_6823988).sum := by decide
  have hdescent : baseEnd_6823988 < baseStart_6823988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6823988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824010 : List Nat := [3, 1, 2, 1, 1, 2, 1, 5, 1, 6]
def baseStart_6824010 : Nat := 118140960795 + 6824010 * 2 ^ 59
def prefixEnd_6824010 : Nat := 4983230072969 + 3 ^ 40 * 6824010 * 2
def baseEnd_6824010 : Nat := 1167999040362650421063985

theorem tailTrace_6824010 : CollatzResearch.WordTrace tailWord_6824010 prefixEnd_6824010 1167999040362650421063985 := by
  unfold tailWord_6824010
  simp only [CollatzResearch.WordTrace]
  refine ⟨62223023001946173241761371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165928061338523128644696989 62223023001946173241761371)
  ·
    refine ⟨93334534502919259862642057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62223023001946173241761371 93334534502919259862642057)
    ·
      refine ⟨70000900877189444896981543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93334534502919259862642057 70000900877189444896981543)
      ·
        refine ⟨105001351315784167345472315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70000900877189444896981543 105001351315784167345472315)
        ·
          refine ⟨157502026973676251018208473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105001351315784167345472315 157502026973676251018208473)
          ·
            refine ⟨118126520230257188263656355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157502026973676251018208473 118126520230257188263656355)
            ·
              refine ⟨177189780345385782395484533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118126520230257188263656355 177189780345385782395484533)
              ·
                refine ⟨16611541907379917099576675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 177189780345385782395484533 16611541907379917099576675)
                ·
                  refine ⟨24917312861069875649365013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16611541907379917099576675 24917312861069875649365013)
                  ·
                    refine ⟨1167999040362650421063985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24917312861069875649365013 1167999040362650421063985)
                    ·
                      rfl

theorem cell23_6824010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_6824010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824010 prefixEnd_6824010 := by exact prefixLift 6824010
  have htrace : WordTrace (prefixWord ++ tailWord_6824010) baseStart_6824010 baseEnd_6824010 := by
    simpa [prefixWord, tailWord_6824010, baseEnd_6824010] using wordTrace_append hprefix tailTrace_6824010
  have hstable : (prefixWord ++ tailWord_6824010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824010).length < 2 ^ (prefixWord ++ tailWord_6824010).sum := by decide
  have hdescent : baseEnd_6824010 < baseStart_6824010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824014 : List Nat := [4, 1, 1, 1, 1, 6, 1, 2, 1, 5]
def baseStart_6824014 : Nat := 118140960795 + 6824014 * 2 ^ 59
def prefixEnd_6824014 : Nat := 4983230072969 + 3 ^ 40 * 6824014 * 2
def baseEnd_6824014 : Nat := 1167999725003523082513979

theorem tailTrace_6824014 : CollatzResearch.WordTrace tailWord_6824014 prefixEnd_6824014 1167999725003523082513979 := by
  unfold tailWord_6824014
  simp only [CollatzResearch.WordTrace]
  refine ⟨31111529737471275206273887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165928158599846801100127397 31111529737471275206273887)
  ·
    refine ⟨46667294606206912809410831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31111529737471275206273887 46667294606206912809410831)
    ·
      refine ⟨70000941909310369214116247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46667294606206912809410831 70000941909310369214116247)
      ·
        refine ⟨105001412863965553821174371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70000941909310369214116247 105001412863965553821174371)
        ·
          refine ⟨157502119295948330731761557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105001412863965553821174371 157502119295948330731761557)
          ·
            refine ⟨7382911841997578003051323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 157502119295948330731761557 7382911841997578003051323)
            ·
              refine ⟨11074367762996367004576985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7382911841997578003051323 11074367762996367004576985)
              ·
                refine ⟨8305775822247275253432739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11074367762996367004576985 8305775822247275253432739)
                ·
                  refine ⟨12458663733370912880149109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8305775822247275253432739 12458663733370912880149109)
                  ·
                    refine ⟨1167999725003523082513979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12458663733370912880149109 1167999725003523082513979)
                    ·
                      rfl

theorem cell23_6824014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_6824014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824014 prefixEnd_6824014 := by exact prefixLift 6824014
  have htrace : WordTrace (prefixWord ++ tailWord_6824014) baseStart_6824014 baseEnd_6824014 := by
    simpa [prefixWord, tailWord_6824014, baseEnd_6824014] using wordTrace_append hprefix tailTrace_6824014
  have hstable : (prefixWord ++ tailWord_6824014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824014).length < 2 ^ (prefixWord ++ tailWord_6824014).sum := by decide
  have hdescent : baseEnd_6824014 < baseStart_6824014 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824037 : List Nat := [1, 3, 1, 3, 2, 2, 3, 1, 1, 1, 5]
def baseStart_6824037 : Nat := 118140960795 + 6824037 * 2 ^ 59
def prefixEnd_6824037 : Nat := 4983230072969 + 3 ^ 40 * 6824037 * 2
def baseEnd_6824037 : Nat := 3504010985065622657554331

theorem tailTrace_6824037 : CollatzResearch.WordTrace tailWord_6824037 prefixEnd_6824037 3504010985065622657554331 := by
  unfold tailWord_6824037
  simp only [CollatzResearch.WordTrace]
  refine ⟨248893076778686876578278365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165928717852457917718852243 248893076778686876578278365)
  ·
    refine ⟨93334903792007578716854387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248893076778686876578278365 93334903792007578716854387)
    ·
      refine ⟨140002355688011368075281581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93334903792007578716854387 140002355688011368075281581)
      ·
        refine ⟨52500883383004263028230593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140002355688011368075281581 52500883383004263028230593)
        ·
          refine ⟨39375662537253197271172945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52500883383004263028230593 39375662537253197271172945)
          ·
            refine ⟨29531746902939897953379709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39375662537253197271172945 29531746902939897953379709)
            ·
              refine ⟨11074405088602461732517391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29531746902939897953379709 11074405088602461732517391)
              ·
                refine ⟨16611607632903692598776087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11074405088602461732517391 16611607632903692598776087)
                ·
                  refine ⟨24917411449355538898164131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16611607632903692598776087 24917411449355538898164131)
                  ·
                    refine ⟨37376117174033308347246197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24917411449355538898164131 37376117174033308347246197)
                    ·
                      refine ⟨3504010985065622657554331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37376117174033308347246197 3504010985065622657554331)
                      ·
                        rfl

theorem cell23_6824037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_6824037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824037 prefixEnd_6824037 := by exact prefixLift 6824037
  have htrace : WordTrace (prefixWord ++ tailWord_6824037) baseStart_6824037 baseEnd_6824037 := by
    simpa [prefixWord, tailWord_6824037, baseEnd_6824037] using wordTrace_append hprefix tailTrace_6824037
  have hstable : (prefixWord ++ tailWord_6824037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824037).length < 2 ^ (prefixWord ++ tailWord_6824037).sum := by decide
  have hdescent : baseEnd_6824037 < baseStart_6824037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824044 : List Nat := [2, 2, 1, 1, 3, 4, 2, 2, 2, 4]
def baseStart_6824044 : Nat := 118140960795 + 6824044 * 2 ^ 59
def prefixEnd_6824044 : Nat := 4983230072969 + 3 ^ 40 * 6824044 * 2
def baseEnd_6824044 : Nat := 1168004859810068043388933

theorem tailTrace_6824044 : CollatzResearch.WordTrace tailWord_6824044 prefixEnd_6824044 1168004859810068043388933 := by
  unfold tailWord_6824044
  simp only [CollatzResearch.WordTrace]
  refine ⟨124446666044830758386891593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165928888059774344515855457 124446666044830758386891593)
  ·
    refine ⟨93334999533623068790168695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124446666044830758386891593 93334999533623068790168695)
    ·
      refine ⟨140002499300434603185253043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93334999533623068790168695 140002499300434603185253043)
      ·
        refine ⟨210003748950651904777879565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140002499300434603185253043 210003748950651904777879565)
        ·
          refine ⟨78751405856494464291704837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210003748950651904777879565 78751405856494464291704837)
          ·
            refine ⟨14765888598092712054694657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78751405856494464291704837 14765888598092712054694657)
            ·
              refine ⟨11074416448569534041020993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14765888598092712054694657 11074416448569534041020993)
              ·
                refine ⟨8305812336427150530765745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11074416448569534041020993 8305812336427150530765745)
                ·
                  refine ⟨6229359252320362898074309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8305812336427150530765745 6229359252320362898074309)
                  ·
                    refine ⟨1168004859810068043388933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6229359252320362898074309 1168004859810068043388933)
                    ·
                      rfl

theorem cell23_6824044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 4].length) (baseStart_6824044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824044 prefixEnd_6824044 := by exact prefixLift 6824044
  have htrace : WordTrace (prefixWord ++ tailWord_6824044) baseStart_6824044 baseEnd_6824044 := by
    simpa [prefixWord, tailWord_6824044, baseEnd_6824044] using wordTrace_append hprefix tailTrace_6824044
  have hstable : (prefixWord ++ tailWord_6824044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824044).length < 2 ^ (prefixWord ++ tailWord_6824044).sum := by decide
  have hdescent : baseEnd_6824044 < baseStart_6824044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824054 : List Nat := [5, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3]
def baseStart_6824054 : Nat := 118140960795 + 6824054 * 2 ^ 59
def prefixEnd_6824054 : Nat := 4983230072969 + 3 ^ 40 * 6824054 * 2
def baseEnd_6824054 : Nat := 3504019714236749091041753

theorem tailTrace_6824054 : CollatzResearch.WordTrace tailWord_6824054 prefixEnd_6824054 3504019714236749091041753 := by
  unfold tailWord_6824054
  simp only [CollatzResearch.WordTrace]
  refine ⟨15555856051226580530102951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165929131213083525654431477 15555856051226580530102951)
  ·
    refine ⟨23333784076839870795154427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15555856051226580530102951 23333784076839870795154427)
    ·
      refine ⟨35000676115259806192731641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23333784076839870795154427 35000676115259806192731641)
      ·
        refine ⟨26250507086444854644548731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35000676115259806192731641 26250507086444854644548731)
        ·
          refine ⟨39375760629667281966823097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26250507086444854644548731 39375760629667281966823097)
          ·
            refine ⟨29531820472250461475117323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39375760629667281966823097 29531820472250461475117323)
            ·
              refine ⟨44297730708375692212675985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29531820472250461475117323 44297730708375692212675985)
              ·
                refine ⟨33223298031281769159506989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44297730708375692212675985 33223298031281769159506989)
                ·
                  refine ⟨12458736761730663434815121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33223298031281769159506989 12458736761730663434815121)
                  ·
                    refine ⟨9344052571297997576111341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12458736761730663434815121 9344052571297997576111341)
                    ·
                      refine ⟨3504019714236749091041753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9344052571297997576111341 3504019714236749091041753)
                      ·
                        rfl

theorem cell23_6824054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_6824054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824054 prefixEnd_6824054 := by exact prefixLift 6824054
  have htrace : WordTrace (prefixWord ++ tailWord_6824054) baseStart_6824054 baseEnd_6824054 := by
    simpa [prefixWord, tailWord_6824054, baseEnd_6824054] using wordTrace_append hprefix tailTrace_6824054
  have hstable : (prefixWord ++ tailWord_6824054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824054).length < 2 ^ (prefixWord ++ tailWord_6824054).sum := by decide
  have hdescent : baseEnd_6824054 < baseStart_6824054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824057 : List Nat := [1, 2, 1, 3, 4, 3, 1, 8]
def baseStart_6824057 : Nat := 118140960795 + 6824057 * 2 ^ 59
def prefixEnd_6824057 : Nat := 4983230072969 + 3 ^ 40 * 6824057 * 2
def baseEnd_6824057 : Nat := 129778564988100465900157

theorem tailTrace_6824057 : CollatzResearch.WordTrace tailWord_6824057 prefixEnd_6824057 129778564988100465900157 := by
  unfold tailWord_6824057
  simp only [CollatzResearch.WordTrace]
  refine ⟨248893806238614419994006425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165929204159076279996004283 248893806238614419994006425)
  ·
    refine ⟨186670354678960814995504819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248893806238614419994006425 186670354678960814995504819)
    ·
      refine ⟨280005532018441222493257229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186670354678960814995504819 280005532018441222493257229)
      ·
        refine ⟨105002074506915458434971461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280005532018441222493257229 105002074506915458434971461)
        ·
          refine ⟨19687888970046648456557149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105002074506915458434971461 19687888970046648456557149)
          ·
            refine ⟨7382958363767493171208931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19687888970046648456557149 7382958363767493171208931)
            ·
              refine ⟨11074437545651239756813397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7382958363767493171208931 11074437545651239756813397)
              ·
                refine ⟨129778564988100465900157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11074437545651239756813397 129778564988100465900157)
                ·
                  rfl

theorem cell23_6824057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 8].length) (baseStart_6824057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824057 prefixEnd_6824057 := by exact prefixLift 6824057
  have htrace : WordTrace (prefixWord ++ tailWord_6824057) baseStart_6824057 baseEnd_6824057 := by
    simpa [prefixWord, tailWord_6824057, baseEnd_6824057] using wordTrace_append hprefix tailTrace_6824057
  have hstable : (prefixWord ++ tailWord_6824057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824057).length < 2 ^ (prefixWord ++ tailWord_6824057).sum := by decide
  have hdescent : baseEnd_6824057 < baseStart_6824057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824067 : List Nat := [1, 1, 1, 3, 3, 3, 1, 3, 1, 3, 3]
def baseStart_6824067 : Nat := 118140960795 + 6824067 * 2 ^ 59
def prefixEnd_6824067 : Nat := 4983230072969 + 3 ^ 40 * 6824067 * 2
def baseEnd_6824067 : Nat := 3504026389485257540179193

theorem tailTrace_6824067 : CollatzResearch.WordTrace tailWord_6824067 prefixEnd_6824067 3504026389485257540179193 := by
  unfold tailWord_6824067
  simp only [CollatzResearch.WordTrace]
  refine ⟨248894170968578191701870455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165929447312385461134580303 248894170968578191701870455)
  ·
    refine ⟨373341256452867287552805683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248894170968578191701870455 373341256452867287552805683)
    ·
      refine ⟨560011884679300931329208525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373341256452867287552805683 560011884679300931329208525)
      ·
        refine ⟨210004456754737849248453197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 560011884679300931329208525 210004456754737849248453197)
        ·
          refine ⟨78751671283026693468169949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210004456754737849248453197 78751671283026693468169949)
          ·
            refine ⟨29531876731135010050563731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78751671283026693468169949 29531876731135010050563731)
            ·
              refine ⟨44297815096702515075845597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29531876731135010050563731 44297815096702515075845597)
              ·
                refine ⟨16611680661263443153442099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44297815096702515075845597 16611680661263443153442099)
                ·
                  refine ⟨24917520991895164730163149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16611680661263443153442099 24917520991895164730163149)
                  ·
                    refine ⟨9344070371960686773811181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24917520991895164730163149 9344070371960686773811181)
                    ·
                      refine ⟨3504026389485257540179193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9344070371960686773811181 3504026389485257540179193)
                      ·
                        rfl

theorem cell23_6824067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3, 3].length) (baseStart_6824067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824067 prefixEnd_6824067 := by exact prefixLift 6824067
  have htrace : WordTrace (prefixWord ++ tailWord_6824067) baseStart_6824067 baseEnd_6824067 := by
    simpa [prefixWord, tailWord_6824067, baseEnd_6824067] using wordTrace_append hprefix tailTrace_6824067
  have hstable : (prefixWord ++ tailWord_6824067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824067).length < 2 ^ (prefixWord ++ tailWord_6824067).sum := by decide
  have hdescent : baseEnd_6824067 < baseStart_6824067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824080 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 5]
def baseStart_6824080 : Nat := 118140960795 + 6824080 * 2 ^ 59
def prefixEnd_6824080 : Nat := 4983230072969 + 3 ^ 40 * 6824080 * 2
def baseEnd_6824080 : Nat := 3504033064733765989316633

theorem tailTrace_6824080 : CollatzResearch.WordTrace tailWord_6824080 prefixEnd_6824080 3504033064733765989316633 := by
  unfold tailWord_6824080
  simp only [CollatzResearch.WordTrace]
  refine ⟨124447322558765547461046847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165929763411687396614729129 124447322558765547461046847)
  ·
    refine ⟨186670983838148321191570271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124447322558765547461046847 186670983838148321191570271)
    ·
      refine ⟨280006475757222481787355407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186670983838148321191570271 280006475757222481787355407)
      ·
        refine ⟨420009713635833722681033111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280006475757222481787355407 420009713635833722681033111)
        ·
          refine ⟨630014570453750584021549667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420009713635833722681033111 630014570453750584021549667)
          ·
            refine ⟨945021855680625876032324501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630014570453750584021549667 945021855680625876032324501)
            ·
              refine ⟨44297899485029337939015211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 945021855680625876032324501 44297899485029337939015211)
              ·
                refine ⟨66446849227544006908522817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44297899485029337939015211 66446849227544006908522817)
                ·
                  refine ⟨49835136920658005181392113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66446849227544006908522817 49835136920658005181392113)
                  ·
                    refine ⟨37376352690493503886044085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49835136920658005181392113 37376352690493503886044085)
                    ·
                      refine ⟨3504033064733765989316633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37376352690493503886044085 3504033064733765989316633)
                      ·
                        rfl

theorem cell23_6824080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 5].length) (baseStart_6824080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824080 prefixEnd_6824080 := by exact prefixLift 6824080
  have htrace : WordTrace (prefixWord ++ tailWord_6824080) baseStart_6824080 baseEnd_6824080 := by
    simpa [prefixWord, tailWord_6824080, baseEnd_6824080] using wordTrace_append hprefix tailTrace_6824080
  have hstable : (prefixWord ++ tailWord_6824080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824080).length < 2 ^ (prefixWord ++ tailWord_6824080).sum := by decide
  have hdescent : baseEnd_6824080 < baseStart_6824080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824088 : List Nat := [2, 1, 2, 4, 3, 2, 2, 1, 1, 2, 3]
def baseStart_6824088 : Nat := 118140960795 + 6824088 * 2 ^ 59
def prefixEnd_6824088 : Nat := 4983230072969 + 3 ^ 40 * 6824088 * 2
def baseEnd_6824088 : Nat := 3504037172579001958016597

theorem tailTrace_6824088 : CollatzResearch.WordTrace tailWord_6824088 prefixEnd_6824088 3504037172579001958016597 := by
  unfold tailWord_6824088
  simp only [CollatzResearch.WordTrace]
  refine ⟨124447468450751056144192459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165929957934334741525589945 124447468450751056144192459)
  ·
    refine ⟨186671202676126584216288689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124447468450751056144192459 186671202676126584216288689)
    ·
      refine ⟨140003402007094938162216517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186671202676126584216288689 140003402007094938162216517)
      ·
        refine ⟨26250637876330300905415597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140003402007094938162216517 26250637876330300905415597)
        ·
          refine ⟨9843989203623862839530849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26250637876330300905415597 9843989203623862839530849)
          ·
            refine ⟨7382991902717897129648137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9843989203623862839530849 7382991902717897129648137)
            ·
              refine ⟨5537243927038422847236103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7382991902717897129648137 5537243927038422847236103)
              ·
                refine ⟨8305865890557634270854155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5537243927038422847236103 8305865890557634270854155)
                ·
                  refine ⟨12458798835836451406281233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8305865890557634270854155 12458798835836451406281233)
                  ·
                    refine ⟨9344099126877338554710925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12458798835836451406281233 9344099126877338554710925)
                    ·
                      refine ⟨3504037172579001958016597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9344099126877338554710925 3504037172579001958016597)
                      ·
                        rfl

theorem cell23_6824088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_6824088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824088 prefixEnd_6824088 := by exact prefixLift 6824088
  have htrace : WordTrace (prefixWord ++ tailWord_6824088) baseStart_6824088 baseEnd_6824088 := by
    simpa [prefixWord, tailWord_6824088, baseEnd_6824088] using wordTrace_append hprefix tailTrace_6824088
  have hstable : (prefixWord ++ tailWord_6824088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824088).length < 2 ^ (prefixWord ++ tailWord_6824088).sum := by decide
  have hdescent : baseEnd_6824088 < baseStart_6824088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824175 : List Nat := [1, 1, 2, 1, 6, 3, 2, 1, 2, 2, 2]
def baseStart_6824175 : Nat := 118140960795 + 6824175 * 2 ^ 59
def prefixEnd_6824175 : Nat := 4983230072969 + 3 ^ 40 * 6824175 * 2
def baseEnd_6824175 : Nat := 3504081845395943117628697

theorem tailTrace_6824175 : CollatzResearch.WordTrace tailWord_6824175 prefixEnd_6824175 3504081845395943117628697 := by
  unfold tailWord_6824175
  simp only [CollatzResearch.WordTrace]
  refine ⟨248898110052186926146801979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165932073368124617431201319 248898110052186926146801979)
  ·
    refine ⟨373347165078280389220202969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248898110052186926146801979 373347165078280389220202969)
    ·
      refine ⟨280010373808710291915152227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373347165078280389220202969 280010373808710291915152227)
      ·
        refine ⟨420015560713065437872728341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280010373808710291915152227 420015560713065437872728341)
        ·
          refine ⟨19688229408424942400284141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 420015560713065437872728341 19688229408424942400284141)
          ·
            refine ⟨7383086028159353400106553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19688229408424942400284141 7383086028159353400106553)
            ·
              refine ⟨5537314521119515050079915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7383086028159353400106553 5537314521119515050079915)
              ·
                refine ⟨8305971781679272575119873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5537314521119515050079915 8305971781679272575119873)
                ·
                  refine ⟨6229478836259454431339905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8305971781679272575119873 6229478836259454431339905)
                  ·
                    refine ⟨4672109127194590823504929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6229478836259454431339905 4672109127194590823504929)
                    ·
                      refine ⟨3504081845395943117628697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4672109127194590823504929 3504081845395943117628697)
                      ·
                        rfl

theorem cell23_6824175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 2, 2, 2].length) (baseStart_6824175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824175 prefixEnd_6824175 := by exact prefixLift 6824175
  have htrace : WordTrace (prefixWord ++ tailWord_6824175) baseStart_6824175 baseEnd_6824175 := by
    simpa [prefixWord, tailWord_6824175, baseEnd_6824175] using wordTrace_append hprefix tailTrace_6824175
  have hstable : (prefixWord ++ tailWord_6824175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824175).length < 2 ^ (prefixWord ++ tailWord_6824175).sum := by decide
  have hdescent : baseEnd_6824175 < baseStart_6824175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824241 : List Nat := [1, 2, 2, 3, 4, 1, 1, 2, 3, 4]
def baseStart_6824241 : Nat := 118140960795 + 6824241 * 2 ^ 59
def prefixEnd_6824241 : Nat := 4983230072969 + 3 ^ 40 * 6824241 * 2
def baseEnd_6824241 : Nat := 1168038578373046619801131

theorem tailTrace_6824241 : CollatzResearch.WordTrace tailWord_6824241 prefixEnd_6824241 1168038578373046619801131 := by
  unfold tailWord_6824241
  simp only [CollatzResearch.WordTrace]
  refine ⟨248900517269947819418704577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165933678179965212945803051 248900517269947819418704577)
  ·
    refine ⟨186675387952460864564028433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248900517269947819418704577 186675387952460864564028433)
    ·
      refine ⟨140006540964345648423021325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186675387952460864564028433 140006540964345648423021325)
      ·
        refine ⟨52502452861629618158632997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140006540964345648423021325 52502452861629618158632997)
        ·
          refine ⟨9844209911555553404743687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52502452861629618158632997 9844209911555553404743687)
          ·
            refine ⟨14766314867333330107115531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9844209911555553404743687 14766314867333330107115531)
            ·
              refine ⟨22149472300999995160673297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14766314867333330107115531 22149472300999995160673297)
              ·
                refine ⟨16612104225749996370504973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22149472300999995160673297 16612104225749996370504973)
                ·
                  refine ⟨6229539084656248638939365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16612104225749996370504973 6229539084656248638939365)
                  ·
                    refine ⟨1168038578373046619801131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6229539084656248638939365 1168038578373046619801131)
                    ·
                      rfl

theorem cell23_6824241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 3, 4].length) (baseStart_6824241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824241 prefixEnd_6824241 := by exact prefixLift 6824241
  have htrace : WordTrace (prefixWord ++ tailWord_6824241) baseStart_6824241 baseEnd_6824241 := by
    simpa [prefixWord, tailWord_6824241, baseEnd_6824241] using wordTrace_append hprefix tailTrace_6824241
  have hstable : (prefixWord ++ tailWord_6824241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824241).length < 2 ^ (prefixWord ++ tailWord_6824241).sum := by decide
  have hdescent : baseEnd_6824241 < baseStart_6824241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824267 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 5, 5]
def baseStart_6824267 : Nat := 118140960795 + 6824267 * 2 ^ 59
def prefixEnd_6824267 : Nat := 4983230072969 + 3 ^ 40 * 6824267 * 2
def baseEnd_6824267 : Nat := 1168043028538718919226091

theorem tailTrace_6824267 : CollatzResearch.WordTrace tailWord_6824267 prefixEnd_6824267 1168043028538718919226091 := by
  unfold tailWord_6824267
  simp only [CollatzResearch.WordTrace]
  refine ⟨248901465567853625859151055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165934310378569083906100703 248901465567853625859151055)
  ·
    refine ⟨373352198351780438788726583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248901465567853625859151055 373352198351780438788726583)
    ·
      refine ⟨560028297527670658183089875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373352198351780438788726583 560028297527670658183089875)
      ·
        refine ⟨840042446291505987274634813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560028297527670658183089875 840042446291505987274634813)
        ·
          refine ⟨315015917359314745227988055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 840042446291505987274634813 315015917359314745227988055)
          ·
            refine ⟨472523876038972117841982083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315015917359314745227988055 472523876038972117841982083)
            ·
              refine ⟨708785814058458176762973125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472523876038972117841982083 708785814058458176762973125)
              ·
                refine ⟨132897340135960908143057461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 708785814058458176762973125 132897340135960908143057461)
                ·
                  refine ⟨12459125637746335138411637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132897340135960908143057461 12459125637746335138411637)
                  ·
                    refine ⟨1168043028538718919226091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12459125637746335138411637 1168043028538718919226091)
                    ·
                      rfl

theorem cell23_6824267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 5].length) (baseStart_6824267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824267 prefixEnd_6824267 := by exact prefixLift 6824267
  have htrace : WordTrace (prefixWord ++ tailWord_6824267) baseStart_6824267 baseEnd_6824267 := by
    simpa [prefixWord, tailWord_6824267, baseEnd_6824267] using wordTrace_append hprefix tailTrace_6824267
  have hstable : (prefixWord ++ tailWord_6824267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824267).length < 2 ^ (prefixWord ++ tailWord_6824267).sum := by decide
  have hdescent : baseEnd_6824267 < baseStart_6824267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824298 : List Nat := [3, 1, 3, 3, 1, 1, 2, 2, 3, 1, 3]
def baseStart_6824298 : Nat := 118140960795 + 6824298 * 2 ^ 59
def prefixEnd_6824298 : Nat := 4983230072969 + 3 ^ 40 * 6824298 * 2
def baseEnd_6824298 : Nat := 3504145003516446136390631

theorem tailTrace_6824298 : CollatzResearch.WordTrace tailWord_6824298 prefixEnd_6824298 3504145003516446136390631 := by
  unfold tailWord_6824298
  simp only [CollatzResearch.WordTrace]
  refine ⟨62225649057685329538382387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165935064153827545435686365 62225649057685329538382387)
  ·
    refine ⟨93338473586527994307573581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62225649057685329538382387 93338473586527994307573581)
    ·
      refine ⟨35001927594947997865340093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93338473586527994307573581 35001927594947997865340093)
      ·
        refine ⟨13125722848105499199502535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35001927594947997865340093 13125722848105499199502535)
        ·
          refine ⟨19688584272158248799253803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13125722848105499199502535 19688584272158248799253803)
          ·
            refine ⟨29532876408237373198880705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19688584272158248799253803 29532876408237373198880705)
            ·
              refine ⟨22149657306178029899160529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29532876408237373198880705 22149657306178029899160529)
              ·
                refine ⟨16612242979633522424370397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22149657306178029899160529 16612242979633522424370397)
                ·
                  refine ⟨6229591117362570909138899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16612242979633522424370397 6229591117362570909138899)
                  ·
                    refine ⟨9344386676043856363708349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6229591117362570909138899 9344386676043856363708349)
                    ·
                      refine ⟨3504145003516446136390631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9344386676043856363708349 3504145003516446136390631)
                      ·
                        rfl

theorem cell23_6824298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_6824298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824298 prefixEnd_6824298 := by exact prefixLift 6824298
  have htrace : WordTrace (prefixWord ++ tailWord_6824298) baseStart_6824298 baseEnd_6824298 := by
    simpa [prefixWord, tailWord_6824298, baseEnd_6824298] using wordTrace_append hprefix tailTrace_6824298
  have hstable : (prefixWord ++ tailWord_6824298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824298).length < 2 ^ (prefixWord ++ tailWord_6824298).sum := by decide
  have hdescent : baseEnd_6824298 < baseStart_6824298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824301 : List Nat := [1, 5, 1, 1, 1, 2, 4, 2, 1, 5]
def baseStart_6824301 : Nat := 118140960795 + 6824301 * 2 ^ 59
def prefixEnd_6824301 : Nat := 4983230072969 + 3 ^ 40 * 6824301 * 2
def baseEnd_6824301 : Nat := 1168048847986136541551039

theorem tailTrace_6824301 : CollatzResearch.WordTrace tailWord_6824301 prefixEnd_6824301 1168048847986136541551039 := by
  unfold tailWord_6824301
  simp only [CollatzResearch.WordTrace]
  refine ⟨248902705649730449665888757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165935137099820299777259171 248902705649730449665888757)
  ·
    refine ⟨23334628654662229656177071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 248902705649730449665888757 23334628654662229656177071)
    ·
      refine ⟨35001942981993344484265607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23334628654662229656177071 35001942981993344484265607)
      ·
        refine ⟨52502914472990016726398411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35001942981993344484265607 52502914472990016726398411)
        ·
          refine ⟨78754371709485025089597617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52502914472990016726398411 78754371709485025089597617)
          ·
            refine ⟨59065778782113768817198213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78754371709485025089597617 59065778782113768817198213)
            ·
              refine ⟨11074833521646331653224665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59065778782113768817198213 11074833521646331653224665)
              ·
                refine ⟨8306125141234748739918499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11074833521646331653224665 8306125141234748739918499)
                ·
                  refine ⟨12459187711852123109877749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8306125141234748739918499 12459187711852123109877749)
                  ·
                    refine ⟨1168048847986136541551039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12459187711852123109877749 1168048847986136541551039)
                    ·
                      rfl

theorem cell23_6824301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_6824301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824301 prefixEnd_6824301 := by exact prefixLift 6824301
  have htrace : WordTrace (prefixWord ++ tailWord_6824301) baseStart_6824301 baseEnd_6824301 := by
    simpa [prefixWord, tailWord_6824301, baseEnd_6824301] using wordTrace_append hprefix tailTrace_6824301
  have hstable : (prefixWord ++ tailWord_6824301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824301).length < 2 ^ (prefixWord ++ tailWord_6824301).sum := by decide
  have hdescent : baseEnd_6824301 < baseStart_6824301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824315 : List Nat := [1, 1, 1, 1, 1, 9, 1, 3, 1, 1, 3]
def baseStart_6824315 : Nat := 118140960795 + 6824315 * 2 ^ 59
def prefixEnd_6824315 : Nat := 4983230072969 + 3 ^ 40 * 6824315 * 2
def baseEnd_6824315 : Nat := 3504153732687572569878053

theorem tailTrace_6824315 : CollatzResearch.WordTrace tailWord_6824315 prefixEnd_6824315 3504153732687572569878053 := by
  unfold tailWord_6824315
  simp only [CollatzResearch.WordTrace]
  refine ⟨248903216271679730056898399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165935477514453153371265599 248903216271679730056898399)
  ·
    refine ⟨373354824407519595085347599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248903216271679730056898399 373354824407519595085347599)
    ·
      refine ⟨560032236611279392628021399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373354824407519595085347599 560032236611279392628021399)
      ·
        refine ⟨840048354916919088942032099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560032236611279392628021399 840048354916919088942032099)
        ·
          refine ⟨1260072532375378633413048149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 840048354916919088942032099 1260072532375378633413048149)
          ·
            refine ⟨7383237494386984180154579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1260072532375378633413048149 7383237494386984180154579)
            ·
              refine ⟨11074856241580476270231869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7383237494386984180154579 11074856241580476270231869)
              ·
                refine ⟨4153071090592678601336951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11074856241580476270231869 4153071090592678601336951)
                ·
                  refine ⟨6229606635889017902005427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4153071090592678601336951 6229606635889017902005427)
                  ·
                    refine ⟨9344409953833526853008141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6229606635889017902005427 9344409953833526853008141)
                    ·
                      refine ⟨3504153732687572569878053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9344409953833526853008141 3504153732687572569878053)
                      ·
                        rfl

theorem cell23_6824315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 3, 1, 1, 3].length) (baseStart_6824315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824315 prefixEnd_6824315 := by exact prefixLift 6824315
  have htrace : WordTrace (prefixWord ++ tailWord_6824315) baseStart_6824315 baseEnd_6824315 := by
    simpa [prefixWord, tailWord_6824315, baseEnd_6824315] using wordTrace_append hprefix tailTrace_6824315
  have hstable : (prefixWord ++ tailWord_6824315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824315).length < 2 ^ (prefixWord ++ tailWord_6824315).sum := by decide
  have hdescent : baseEnd_6824315 < baseStart_6824315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824337 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 7]
def baseStart_6824337 : Nat := 118140960795 + 6824337 * 2 ^ 59
def prefixEnd_6824337 : Nat := 4983230072969 + 3 ^ 40 * 6824337 * 2
def baseEnd_6824337 : Nat := 3504165029261971483802951

theorem tailTrace_6824337 : CollatzResearch.WordTrace tailWord_6824337 prefixEnd_6824337 3504165029261971483802951 := by
  unfold tailWord_6824337
  simp only [CollatzResearch.WordTrace]
  refine ⟨248904018677600027814199265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165936012451733351876132843 248904018677600027814199265)
  ·
    refine ⟨186678014008200020860649449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248904018677600027814199265 186678014008200020860649449)
    ·
      refine ⟨140008510506150015645487087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186678014008200020860649449 140008510506150015645487087)
      ·
        refine ⟨210012765759225023468230631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140008510506150015645487087 210012765759225023468230631)
        ·
          refine ⟨315019148638837535202345947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210012765759225023468230631 315019148638837535202345947)
          ·
            refine ⟨472528722958256302803518921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315019148638837535202345947 472528722958256302803518921)
            ·
              refine ⟨354396542218692227102639191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472528722958256302803518921 354396542218692227102639191)
              ·
                refine ⟨531594813328038340653958787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354396542218692227102639191 531594813328038340653958787)
                ·
                  refine ⟨797392219992057510980938181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 531594813328038340653958787 797392219992057510980938181)
                  ·
                    refine ⟨149511041248510783308925909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 797392219992057510980938181 149511041248510783308925909)
                    ·
                      refine ⟨3504165029261971483802951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149511041248510783308925909 3504165029261971483802951)
                      ·
                        rfl

theorem cell23_6824337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_6824337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824337 prefixEnd_6824337 := by exact prefixLift 6824337
  have htrace : WordTrace (prefixWord ++ tailWord_6824337) baseStart_6824337 baseEnd_6824337 := by
    simpa [prefixWord, tailWord_6824337, baseEnd_6824337] using wordTrace_append hprefix tailTrace_6824337
  have hstable : (prefixWord ++ tailWord_6824337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824337).length < 2 ^ (prefixWord ++ tailWord_6824337).sum := by decide
  have hdescent : baseEnd_6824337 < baseStart_6824337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824344 : List Nat := [2, 1, 2, 5, 1, 1, 1, 10]
def baseStart_6824344 : Nat := 118140960795 + 6824344 * 2 ^ 59
def prefixEnd_6824344 : Nat := 4983230072969 + 3 ^ 40 * 6824344 * 2
def baseEnd_6824344 : Nat := 129784023097279739126497

theorem tailTrace_6824344 : CollatzResearch.WordTrace tailWord_6824344 prefixEnd_6824344 129784023097279739126497 := by
  unfold tailWord_6824344
  simp only [CollatzResearch.WordTrace]
  refine ⟨124452136994287334004852043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165936182659049778673136057 124452136994287334004852043)
  ·
    refine ⟨186678205491431001007278065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124452136994287334004852043 186678205491431001007278065)
    ·
      refine ⟨140008654118573250755458549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186678205491431001007278065 140008654118573250755458549)
      ·
        refine ⟨13125811323616242258324239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140008654118573250755458549 13125811323616242258324239)
        ·
          refine ⟨19688716985424363387486359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13125811323616242258324239 19688716985424363387486359)
          ·
            refine ⟨29533075478136545081229539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19688716985424363387486359 29533075478136545081229539)
            ·
              refine ⟨44299613217204817621844309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29533075478136545081229539 44299613217204817621844309)
              ·
                refine ⟨129784023097279739126497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 44299613217204817621844309 129784023097279739126497)
                ·
                  rfl

theorem cell23_6824344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 10].length) (baseStart_6824344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824344 prefixEnd_6824344 := by exact prefixLift 6824344
  have htrace : WordTrace (prefixWord ++ tailWord_6824344) baseStart_6824344 baseEnd_6824344 := by
    simpa [prefixWord, tailWord_6824344, baseEnd_6824344] using wordTrace_append hprefix tailTrace_6824344
  have hstable : (prefixWord ++ tailWord_6824344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824344).length < 2 ^ (prefixWord ++ tailWord_6824344).sum := by decide
  have hdescent : baseEnd_6824344 < baseStart_6824344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824394 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 1, 5, 4]
def baseStart_6824394 : Nat := 118140960795 + 6824394 * 2 ^ 59
def prefixEnd_6824394 : Nat := 4983230072969 + 3 ^ 40 * 6824394 * 2
def baseEnd_6824394 : Nat := 3504194297659277760790189

theorem tailTrace_6824394 : CollatzResearch.WordTrace tailWord_6824394 prefixEnd_6824394 3504194297659277760790189 := by
  unfold tailWord_6824394
  simp only [CollatzResearch.WordTrace]
  refine ⟨62226524409598381637256059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165937398425595684366016157 62226524409598381637256059)
  ·
    refine ⟨93339786614397572455884089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62226524409598381637256059 93339786614397572455884089)
    ·
      refine ⟨70004839960798179341913067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93339786614397572455884089 70004839960798179341913067)
      ·
        refine ⟨105007259941197269012869601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70004839960798179341913067 105007259941197269012869601)
        ·
          refine ⟨78755444955897951759652201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105007259941197269012869601 78755444955897951759652201)
          ·
            refine ⟨59066583716923463819739151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78755444955897951759652201 59066583716923463819739151)
            ·
              refine ⟨88599875575385195729608727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59066583716923463819739151 88599875575385195729608727)
              ·
                refine ⟨132899813363077793594413091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88599875575385195729608727 132899813363077793594413091)
                ·
                  refine ⟨199349720044616690391619637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132899813363077793594413091 199349720044616690391619637)
                  ·
                    refine ⟨18689036254182814724214341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 199349720044616690391619637 18689036254182814724214341)
                    ·
                      refine ⟨3504194297659277760790189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18689036254182814724214341 3504194297659277760790189)
                      ·
                        rfl

theorem cell23_6824394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_6824394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824394 prefixEnd_6824394 := by exact prefixLift 6824394
  have htrace : WordTrace (prefixWord ++ tailWord_6824394) baseStart_6824394 baseEnd_6824394 := by
    simpa [prefixWord, tailWord_6824394, baseEnd_6824394] using wordTrace_append hprefix tailTrace_6824394
  have hstable : (prefixWord ++ tailWord_6824394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824394).length < 2 ^ (prefixWord ++ tailWord_6824394).sum := by decide
  have hdescent : baseEnd_6824394 < baseStart_6824394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824428 : List Nat := [2, 2, 1, 1, 2, 1, 4, 2, 4, 2, 2]
def baseStart_6824428 : Nat := 118140960795 + 6824428 * 2 ^ 59
def prefixEnd_6824428 : Nat := 4983230072969 + 3 ^ 40 * 6824428 * 2
def baseEnd_6824428 : Nat := 3504211756001530627765033

theorem tailTrace_6824428 : CollatzResearch.WordTrace tailWord_6824428 prefixEnd_6824428 3504211756001530627765033 := by
  unfold tailWord_6824428
  simp only [CollatzResearch.WordTrace]
  refine ⟨124453668860135175177880969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165938225146846900237174625 124453668860135175177880969)
  ·
    refine ⟨93340251645101381383410727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124453668860135175177880969 93340251645101381383410727)
    ·
      refine ⟨140010377467652072075116091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93340251645101381383410727 140010377467652072075116091)
      ·
        refine ⟨210015566201478108112674137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140010377467652072075116091 210015566201478108112674137)
        ·
          refine ⟨157511674651108581084505603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210015566201478108112674137 157511674651108581084505603)
          ·
            refine ⟨236267511976662871626758405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157511674651108581084505603 236267511976662871626758405)
            ·
              refine ⟨44300158495624288430017201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 236267511976662871626758405 44300158495624288430017201)
              ·
                refine ⟨33225118871718216322512901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44300158495624288430017201 33225118871718216322512901)
                ·
                  refine ⟨6229709788447165560471169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33225118871718216322512901 6229709788447165560471169)
                  ·
                    refine ⟨4672282341335374170353377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6229709788447165560471169 4672282341335374170353377)
                    ·
                      refine ⟨3504211756001530627765033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4672282341335374170353377 3504211756001530627765033)
                      ·
                        rfl

theorem cell23_6824428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 2, 2].length) (baseStart_6824428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824428 prefixEnd_6824428 := by exact prefixLift 6824428
  have htrace : WordTrace (prefixWord ++ tailWord_6824428) baseStart_6824428 baseEnd_6824428 := by
    simpa [prefixWord, tailWord_6824428, baseEnd_6824428] using wordTrace_append hprefix tailTrace_6824428
  have hstable : (prefixWord ++ tailWord_6824428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824428).length < 2 ^ (prefixWord ++ tailWord_6824428).sum := by decide
  have hdescent : baseEnd_6824428 < baseStart_6824428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824451 : List Nat := [1, 1, 1, 3, 2, 1, 3, 6, 5]
def baseStart_6824451 : Nat := 118140960795 + 6824451 * 2 ^ 59
def prefixEnd_6824451 : Nat := 4983230072969 + 3 ^ 40 * 6824451 * 2
def baseEnd_6824451 : Nat := 389358174006287115308603

theorem tailTrace_6824451 : CollatzResearch.WordTrace tailWord_6824451 prefixEnd_6824451 389358174006287115308603 := by
  unfold tailWord_6824451
  simp only [CollatzResearch.WordTrace]
  refine ⟨248908176599187025283849207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165938784399458016855899471 248908176599187025283849207)
  ·
    refine ⟨373362264898780537925773811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248908176599187025283849207 373362264898780537925773811)
    ·
      refine ⟨560043397348170806888660717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373362264898780537925773811 560043397348170806888660717)
      ·
        refine ⟨210016274005564052583247769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 560043397348170806888660717 210016274005564052583247769)
        ·
          refine ⟨157512205504173039437435827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210016274005564052583247769 157512205504173039437435827)
          ·
            refine ⟨236268308256259559156153741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157512205504173039437435827 236268308256259559156153741)
            ·
              refine ⟨88600615596097334683557653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236268308256259559156153741 88600615596097334683557653)
              ·
                refine ⟨4153153856067062563291765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88600615596097334683557653 4153153856067062563291765)
                ·
                  refine ⟨389358174006287115308603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4153153856067062563291765 389358174006287115308603)
                  ·
                    rfl

theorem cell23_6824451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 6, 5].length) (baseStart_6824451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824451 prefixEnd_6824451 := by exact prefixLift 6824451
  have htrace : WordTrace (prefixWord ++ tailWord_6824451) baseStart_6824451 baseEnd_6824451 := by
    simpa [prefixWord, tailWord_6824451, baseEnd_6824451] using wordTrace_append hprefix tailTrace_6824451
  have hstable : (prefixWord ++ tailWord_6824451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824451).length < 2 ^ (prefixWord ++ tailWord_6824451).sum := by decide
  have hdescent : baseEnd_6824451 < baseStart_6824451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824468 : List Nat := [2, 4, 3, 1, 1, 1, 2, 2, 7]
def baseStart_6824468 : Nat := 118140960795 + 6824468 * 2 ^ 59
def prefixEnd_6824468 : Nat := 4983230072969 + 3 ^ 40 * 6824468 * 2
def baseEnd_6824468 : Nat := 389359143914190052362761

theorem tailTrace_6824468 : CollatzResearch.WordTrace tailWord_6824468 prefixEnd_6824468 389359143914190052362761 := by
  unfold tailWord_6824468
  simp only [CollatzResearch.WordTrace]
  refine ⟨124454398320062718593609029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165939197760083624791478705 124454398320062718593609029)
  ·
    refine ⟨23335199685011759736301693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124454398320062718593609029 23335199685011759736301693)
    ·
      refine ⟨8750699881879409901113135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23335199685011759736301693 8750699881879409901113135)
      ·
        refine ⟨13126049822819114851669703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8750699881879409901113135 13126049822819114851669703)
        ·
          refine ⟨19689074734228672277504555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13126049822819114851669703 19689074734228672277504555)
          ·
            refine ⟨29533612101343008416256833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19689074734228672277504555 29533612101343008416256833)
            ·
              refine ⟨22150209076007256312192625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29533612101343008416256833 22150209076007256312192625)
              ·
                refine ⟨16612656807005442234144469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22150209076007256312192625 16612656807005442234144469)
                ·
                  refine ⟨389359143914190052362761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16612656807005442234144469 389359143914190052362761)
                  ·
                    rfl

theorem cell23_6824468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_6824468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824468 prefixEnd_6824468 := by exact prefixLift 6824468
  have htrace : WordTrace (prefixWord ++ tailWord_6824468) baseStart_6824468 baseEnd_6824468 := by
    simpa [prefixWord, tailWord_6824468, baseEnd_6824468] using wordTrace_append hprefix tailTrace_6824468
  have hstable : (prefixWord ++ tailWord_6824468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824468).length < 2 ^ (prefixWord ++ tailWord_6824468).sum := by decide
  have hdescent : baseEnd_6824468 < baseStart_6824468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824481 : List Nat := [1, 2, 3, 2, 2, 1, 2, 3, 2, 5]
def baseStart_6824481 : Nat := 118140960795 + 6824481 * 2 ^ 59
def prefixEnd_6824481 : Nat := 4983230072969 + 3 ^ 40 * 6824481 * 2
def baseEnd_6824481 : Nat := 1168079656825406306800763

theorem tailTrace_6824481 : CollatzResearch.WordTrace tailWord_6824481 prefixEnd_6824481 1168079656825406306800763 := by
  unfold tailWord_6824481
  simp only [CollatzResearch.WordTrace]
  refine ⟨248909270789078340407441297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165939513859385560271627531 248909270789078340407441297)
  ·
    refine ⟨186681953091808755305580973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248909270789078340407441297 186681953091808755305580973)
    ·
      refine ⟨70005732409428283239592865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186681953091808755305580973 70005732409428283239592865)
      ·
        refine ⟨52504299307071212429694649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70005732409428283239592865 52504299307071212429694649)
        ·
          refine ⟨39378224480303409322270987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52504299307071212429694649 39378224480303409322270987)
          ·
            refine ⟨59067336720455113983406481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39378224480303409322270987 59067336720455113983406481)
            ·
              refine ⟨44300502540341335487554861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59067336720455113983406481 44300502540341335487554861)
              ·
                refine ⟨16612688452628000807833073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44300502540341335487554861 16612688452628000807833073)
                ·
                  refine ⟨12459516339471000605874805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16612688452628000807833073 12459516339471000605874805)
                  ·
                    refine ⟨1168079656825406306800763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12459516339471000605874805 1168079656825406306800763)
                    ·
                      rfl

theorem cell23_6824481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_6824481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824481 prefixEnd_6824481 := by exact prefixLift 6824481
  have htrace : WordTrace (prefixWord ++ tailWord_6824481) baseStart_6824481 baseEnd_6824481 := by
    simpa [prefixWord, tailWord_6824481, baseEnd_6824481] using wordTrace_append hprefix tailTrace_6824481
  have hstable : (prefixWord ++ tailWord_6824481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824481).length < 2 ^ (prefixWord ++ tailWord_6824481).sum := by decide
  have hdescent : baseEnd_6824481 < baseStart_6824481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824502 : List Nat := [5, 1, 2, 1, 2, 2, 3, 2, 5]
def baseStart_6824502 : Nat := 118140960795 + 6824502 * 2 ^ 59
def prefixEnd_6824502 : Nat := 4983230072969 + 3 ^ 40 * 6824502 * 2
def baseEnd_6824502 : Nat := 389361083729995926471077

theorem tailTrace_6824502 : CollatzResearch.WordTrace tailWord_6824502 prefixEnd_6824502 389361083729995926471077 := by
  unfold tailWord_6824502
  simp only [CollatzResearch.WordTrace]
  refine ⟨15556877295125141312122235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165940024481334840662637173 15556877295125141312122235)
  ·
    refine ⟨23335315942687711968183353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15556877295125141312122235 23335315942687711968183353)
    ·
      refine ⟨17501486957015783976137515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23335315942687711968183353 17501486957015783976137515)
      ·
        refine ⟨26252230435523675964206273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17501486957015783976137515 26252230435523675964206273)
        ·
          refine ⟨19689172826642756973154705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26252230435523675964206273 19689172826642756973154705)
          ·
            refine ⟨14766879619982067729866029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19689172826642756973154705 14766879619982067729866029)
            ·
              refine ⟨5537579857493275398699761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14766879619982067729866029 5537579857493275398699761)
              ·
                refine ⟨4153184893119956549024821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5537579857493275398699761 4153184893119956549024821)
                ·
                  refine ⟨389361083729995926471077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4153184893119956549024821 389361083729995926471077)
                  ·
                    rfl

theorem cell23_6824502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_6824502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824502 prefixEnd_6824502 := by exact prefixLift 6824502
  have htrace : WordTrace (prefixWord ++ tailWord_6824502) baseStart_6824502 baseEnd_6824502 := by
    simpa [prefixWord, tailWord_6824502, baseEnd_6824502] using wordTrace_append hprefix tailTrace_6824502
  have hstable : (prefixWord ++ tailWord_6824502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824502).length < 2 ^ (prefixWord ++ tailWord_6824502).sum := by decide
  have hdescent : baseEnd_6824502 < baseStart_6824502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824558 : List Nat := [4, 1, 2, 2, 2, 1, 1, 4, 6]
def baseStart_6824558 : Nat := 118140960795 + 6824558 * 2 ^ 59
def prefixEnd_6824558 : Nat := 4983230072969 + 3 ^ 40 * 6824558 * 2
def baseEnd_6824558 : Nat := 389364278720735013237715

theorem tailTrace_6824558 : CollatzResearch.WordTrace tailWord_6824558 prefixEnd_6824558 389364278720735013237715 := by
  unfold tailWord_6824558
  simp only [CollatzResearch.WordTrace]
  refine ⟨31114009901224922819749291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165941386139866255038662885 31114009901224922819749291)
  ·
    refine ⟨46671014851837384229623937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31114009901224922819749291 46671014851837384229623937)
    ·
      refine ⟨35003261138878038172217953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46671014851837384229623937 35003261138878038172217953)
      ·
        refine ⟨26252445854158528629163465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35003261138878038172217953 26252445854158528629163465)
        ·
          refine ⟨19689334390618896471872599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26252445854158528629163465 19689334390618896471872599)
          ·
            refine ⟨29534001585928344707808899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19689334390618896471872599 29534001585928344707808899)
            ·
              refine ⟨44301002378892517061713349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29534001585928344707808899 44301002378892517061713349)
              ·
                refine ⟨8306437946042346949071253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44301002378892517061713349 8306437946042346949071253)
                ·
                  refine ⟨389364278720735013237715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8306437946042346949071253 389364278720735013237715)
                  ·
                    rfl

theorem cell23_6824558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 6].length) (baseStart_6824558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824558 prefixEnd_6824558 := by exact prefixLift 6824558
  have htrace : WordTrace (prefixWord ++ tailWord_6824558) baseStart_6824558 baseEnd_6824558 := by
    simpa [prefixWord, tailWord_6824558, baseEnd_6824558] using wordTrace_append hprefix tailTrace_6824558
  have hstable : (prefixWord ++ tailWord_6824558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824558).length < 2 ^ (prefixWord ++ tailWord_6824558).sum := by decide
  have hdescent : baseEnd_6824558 < baseStart_6824558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824562 : List Nat := [3, 2, 1, 2, 4, 1, 1, 4, 1, 4]
def baseStart_6824562 : Nat := 118140960795 + 6824562 * 2 ^ 59
def prefixEnd_6824562 : Nat := 4983230072969 + 3 ^ 40 * 6824562 * 2
def baseEnd_6824562 : Nat := 1168093520803077701163139

theorem tailTrace_6824562 : CollatzResearch.WordTrace tailWord_6824562 prefixEnd_6824562 1168093520803077701163139 := by
  unfold tailWord_6824562
  simp only [CollatzResearch.WordTrace]
  refine ⟨62228056275446222810284985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165941483401189927494093293 62228056275446222810284985)
  ·
    refine ⟨46671042206584667107713739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62228056275446222810284985 46671042206584667107713739)
    ·
      refine ⟨70006563309877000661570609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46671042206584667107713739 70006563309877000661570609)
      ·
        refine ⟨52504922482407750496177957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70006563309877000661570609 52504922482407750496177957)
        ·
          refine ⟨9844672965451453218033367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52504922482407750496177957 9844672965451453218033367)
          ·
            refine ⟨14767009448177179827050051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9844672965451453218033367 14767009448177179827050051)
            ·
              refine ⟨22150514172265769740575077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14767009448177179827050051 22150514172265769740575077)
              ·
                refine ⟨4153221407299831826357827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22150514172265769740575077 4153221407299831826357827)
                ·
                  refine ⟨6229832110949747739536741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4153221407299831826357827 6229832110949747739536741)
                  ·
                    refine ⟨1168093520803077701163139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6229832110949747739536741 1168093520803077701163139)
                    ·
                      rfl

theorem cell23_6824562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_6824562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824562 prefixEnd_6824562 := by exact prefixLift 6824562
  have htrace : WordTrace (prefixWord ++ tailWord_6824562) baseStart_6824562 baseEnd_6824562 := by
    simpa [prefixWord, tailWord_6824562, baseEnd_6824562] using wordTrace_append hprefix tailTrace_6824562
  have hstable : (prefixWord ++ tailWord_6824562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824562).length < 2 ^ (prefixWord ++ tailWord_6824562).sum := by decide
  have hdescent : baseEnd_6824562 < baseStart_6824562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824601 : List Nat := [1, 2, 1, 2, 1, 2, 3, 4, 1, 6]
def baseStart_6824601 : Nat := 118140960795 + 6824601 * 2 ^ 59
def prefixEnd_6824601 : Nat := 4983230072969 + 3 ^ 40 * 6824601 * 2
def baseEnd_6824601 : Nat := 1168100196051586150300579

theorem tailTrace_6824601 : CollatzResearch.WordTrace tailWord_6824601 prefixEnd_6824601 1168100196051586150300579 := by
  unfold tailWord_6824601
  simp only [CollatzResearch.WordTrace]
  refine ⟨248913647548643600901809657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165942431699095733934539771 248913647548643600901809657)
  ·
    refine ⟨186685235661482700676357243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248913647548643600901809657 186685235661482700676357243)
    ·
      refine ⟨280027853492224051014535865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186685235661482700676357243 280027853492224051014535865)
      ·
        refine ⟨210020890119168038260901899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280027853492224051014535865 210020890119168038260901899)
        ·
          refine ⟨315031335178752057391352849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210020890119168038260901899 315031335178752057391352849)
          ·
            refine ⟨236273501384064043043514637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315031335178752057391352849 236273501384064043043514637)
            ·
              refine ⟨88602563019024016141317989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236273501384064043043514637 88602563019024016141317989)
              ·
                refine ⟨16612980566067003026497123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88602563019024016141317989 16612980566067003026497123)
                ·
                  refine ⟨24919470849100504539745685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16612980566067003026497123 24919470849100504539745685)
                  ·
                    refine ⟨1168100196051586150300579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24919470849100504539745685 1168100196051586150300579)
                    ·
                      rfl

theorem cell23_6824601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 6].length) (baseStart_6824601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824601 prefixEnd_6824601 := by exact prefixLift 6824601
  have htrace : WordTrace (prefixWord ++ tailWord_6824601) baseStart_6824601 baseEnd_6824601 := by
    simpa [prefixWord, tailWord_6824601, baseEnd_6824601] using wordTrace_append hprefix tailTrace_6824601
  have hstable : (prefixWord ++ tailWord_6824601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824601).length < 2 ^ (prefixWord ++ tailWord_6824601).sum := by decide
  have hdescent : baseEnd_6824601 < baseStart_6824601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824605 : List Nat := [1, 4, 2, 1, 1, 1, 6, 1, 1, 5]
def baseStart_6824605 : Nat := 118140960795 + 6824605 * 2 ^ 59
def prefixEnd_6824605 : Nat := 4983230072969 + 3 ^ 40 * 6824605 * 2
def baseEnd_6824605 : Nat := 1168100880692458811750573

theorem tailTrace_6824605 : CollatzResearch.WordTrace tailWord_6824605 prefixEnd_6824605 1168100880692458811750573 := by
  unfold tailWord_6824605
  simp only [CollatzResearch.WordTrace]
  refine ⟨248913793440629109584955269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165942528960419406389970179 248913793440629109584955269)
  ·
    refine ⟨46671336270117958047179113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248913793440629109584955269 46671336270117958047179113)
    ·
      refine ⟨35003502202588468535384335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46671336270117958047179113 35003502202588468535384335)
      ·
        refine ⟨52505253303882702803076503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35003502202588468535384335 52505253303882702803076503)
        ·
          refine ⟨78757879955824054204614755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52505253303882702803076503 78757879955824054204614755)
          ·
            refine ⟨118136819933736081306922133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78757879955824054204614755 118136819933736081306922133)
            ·
              refine ⟨5537663434393878811261975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118136819933736081306922133 5537663434393878811261975)
              ·
                refine ⟨8306495151590818216892963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5537663434393878811261975 8306495151590818216892963)
                ·
                  refine ⟨12459742727386227325339445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8306495151590818216892963 12459742727386227325339445)
                  ·
                    refine ⟨1168100880692458811750573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12459742727386227325339445 1168100880692458811750573)
                    ·
                      rfl

theorem cell23_6824605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_6824605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824605 prefixEnd_6824605 := by exact prefixLift 6824605
  have htrace : WordTrace (prefixWord ++ tailWord_6824605) baseStart_6824605 baseEnd_6824605 := by
    simpa [prefixWord, tailWord_6824605, baseEnd_6824605] using wordTrace_append hprefix tailTrace_6824605
  have hstable : (prefixWord ++ tailWord_6824605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824605).length < 2 ^ (prefixWord ++ tailWord_6824605).sum := by decide
  have hdescent : baseEnd_6824605 < baseStart_6824605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824638 : List Nat := [4, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6]
def baseStart_6824638 : Nat := 118140960795 + 6824638 * 2 ^ 59
def prefixEnd_6824638 : Nat := 4983230072969 + 3 ^ 40 * 6824638 * 2
def baseEnd_6824638 : Nat := 3504319586938974806139067

theorem tailTrace_6824638 : CollatzResearch.WordTrace tailWord_6824638 prefixEnd_6824638 3504319586938974806139067 := by
  unfold tailWord_6824638
  simp only [CollatzResearch.WordTrace]
  refine ⟨31114374631188694527613321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165943331366339704147271045 31114374631188694527613321)
  ·
    refine ⟨23335780973391520895709991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31114374631188694527613321 23335780973391520895709991)
    ·
      refine ⟨35003671460087281343564987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23335780973391520895709991 35003671460087281343564987)
      ·
        refine ⟨52505507190130922015347481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35003671460087281343564987 52505507190130922015347481)
        ·
          refine ⟨39379130392598191511510611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52505507190130922015347481 39379130392598191511510611)
          ·
            refine ⟨59068695588897287267265917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39379130392598191511510611 59068695588897287267265917)
            ·
              refine ⟨22150760845836482725224719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59068695588897287267265917 22150760845836482725224719)
              ·
                refine ⟨33226141268754724087837079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22150760845836482725224719 33226141268754724087837079)
                ·
                  refine ⟨49839211903132086131755619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33226141268754724087837079 49839211903132086131755619)
                  ·
                    refine ⟨74758817854698129197633429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49839211903132086131755619 74758817854698129197633429)
                    ·
                      refine ⟨3504319586938974806139067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74758817854698129197633429 3504319586938974806139067)
                      ·
                        rfl

theorem cell23_6824638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_6824638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824638 prefixEnd_6824638 := by exact prefixLift 6824638
  have htrace : WordTrace (prefixWord ++ tailWord_6824638) baseStart_6824638 baseEnd_6824638 := by
    simpa [prefixWord, tailWord_6824638, baseEnd_6824638] using wordTrace_append hprefix tailTrace_6824638
  have hstable : (prefixWord ++ tailWord_6824638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824638).length < 2 ^ (prefixWord ++ tailWord_6824638).sum := by decide
  have hdescent : baseEnd_6824638 < baseStart_6824638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824648 : List Nat := [2, 1, 3, 1, 2, 3, 4, 7]
def baseStart_6824648 : Nat := 118140960795 + 6824648 * 2 ^ 59
def prefixEnd_6824648 : Nat := 4983230072969 + 3 ^ 40 * 6824648 * 2
def baseEnd_6824648 : Nat := 129789804509093324704223

theorem tailTrace_6824648 : CollatzResearch.WordTrace tailWord_6824648 prefixEnd_6824648 129789804509093324704223 := by
  unfold tailWord_6824648
  simp only [CollatzResearch.WordTrace]
  refine ⟨124457680889736663964385299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165943574519648885285847065 124457680889736663964385299)
  ·
    refine ⟨186686521334604995946577949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124457680889736663964385299 186686521334604995946577949)
    ·
      refine ⟨70007445500476873479966731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186686521334604995946577949 70007445500476873479966731)
      ·
        refine ⟨105011168250715310219950097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70007445500476873479966731 105011168250715310219950097)
        ·
          refine ⟨78758376188036482664962573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105011168250715310219950097 78758376188036482664962573)
          ·
            refine ⟨29534391070513680999360965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78758376188036482664962573 29534391070513680999360965)
            ·
              refine ⟨5537698325721315187380181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29534391070513680999360965 5537698325721315187380181)
              ·
                refine ⟨129789804509093324704223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5537698325721315187380181 129789804509093324704223)
                ·
                  rfl

theorem cell23_6824648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 7].length) (baseStart_6824648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824648 prefixEnd_6824648 := by exact prefixLift 6824648
  have htrace : WordTrace (prefixWord ++ tailWord_6824648) baseStart_6824648 baseEnd_6824648 := by
    simpa [prefixWord, tailWord_6824648, baseEnd_6824648] using wordTrace_append hprefix tailTrace_6824648
  have hstable : (prefixWord ++ tailWord_6824648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824648).length < 2 ^ (prefixWord ++ tailWord_6824648).sum := by decide
  have hdescent : baseEnd_6824648 < baseStart_6824648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824653 : List Nat := [1, 6, 2, 1, 2, 2, 1, 3, 1, 1, 3]
def baseStart_6824653 : Nat := 118140960795 + 6824653 * 2 ^ 59
def prefixEnd_6824653 : Nat := 4983230072969 + 3 ^ 40 * 6824653 * 2
def baseEnd_6824653 : Nat := 3504327289148792247451499

theorem tailTrace_6824653 : CollatzResearch.WordTrace tailWord_6824653 prefixEnd_6824653 3504327289148792247451499 := by
  unfold tailWord_6824653
  simp only [CollatzResearch.WordTrace]
  refine ⟨248915544144455213782702613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165943696096303475855135075 248915544144455213782702613)
  ·
    refine ⟨11667916131771338146064185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 248915544144455213782702613 11667916131771338146064185)
    ·
      refine ⟨8750937098828503609548139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11667916131771338146064185 8750937098828503609548139)
      ·
        refine ⟨13126405648242755414322209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8750937098828503609548139 13126405648242755414322209)
        ·
          refine ⟨9844804236182066560741657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13126405648242755414322209 9844804236182066560741657)
          ·
            refine ⟨7383603177136549920556243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9844804236182066560741657 7383603177136549920556243)
            ·
              refine ⟨11075404765704824880834365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7383603177136549920556243 11075404765704824880834365)
              ·
                refine ⟨4153276787139309330312887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11075404765704824880834365 4153276787139309330312887)
                ·
                  refine ⟨6229915180708963995469331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4153276787139309330312887 6229915180708963995469331)
                  ·
                    refine ⟨9344872771063445993203997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6229915180708963995469331 9344872771063445993203997)
                    ·
                      refine ⟨3504327289148792247451499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9344872771063445993203997 3504327289148792247451499)
                      ·
                        rfl

theorem cell23_6824653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_6824653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824653 prefixEnd_6824653 := by exact prefixLift 6824653
  have htrace : WordTrace (prefixWord ++ tailWord_6824653) baseStart_6824653 baseEnd_6824653 := by
    simpa [prefixWord, tailWord_6824653, baseEnd_6824653] using wordTrace_append hprefix tailTrace_6824653
  have hstable : (prefixWord ++ tailWord_6824653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824653).length < 2 ^ (prefixWord ++ tailWord_6824653).sum := by decide
  have hdescent : baseEnd_6824653 < baseStart_6824653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824676 : List Nat := [2, 3, 1, 1, 1, 5, 3, 2, 1, 2, 2]
def baseStart_6824676 : Nat := 118140960795 + 6824676 * 2 ^ 59
def prefixEnd_6824676 : Nat := 4983230072969 + 3 ^ 40 * 6824676 * 2
def baseEnd_6824676 : Nat := 3504339099203845657463893

theorem tailTrace_6824676 : CollatzResearch.WordTrace tailWord_6824676 prefixEnd_6824676 3504339099203845657463893 := by
  unfold tailWord_6824676
  simp only [CollatzResearch.WordTrace]
  refine ⟨124458191511685944355394941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165944255348914592473859921 124458191511685944355394941)
  ·
    refine ⟨46671821816882229133273103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124458191511685944355394941 46671821816882229133273103)
    ·
      refine ⟨70007732725323343699909655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46671821816882229133273103 70007732725323343699909655)
      ·
        refine ⟨105011599087985015549864483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70007732725323343699909655 105011599087985015549864483)
        ·
          refine ⟨157517398631977523324796725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105011599087985015549864483 157517398631977523324796725)
          ·
            refine ⟨14767256121747892811699693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157517398631977523324796725 14767256121747892811699693)
            ·
              refine ⟨5537721045655459804387385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14767256121747892811699693 5537721045655459804387385)
              ·
                refine ⟨4153290784241594853290539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5537721045655459804387385 4153290784241594853290539)
                ·
                  refine ⟨6229936176362392279935809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4153290784241594853290539 6229936176362392279935809)
                  ·
                    refine ⟨4672452132271794209951857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6229936176362392279935809 4672452132271794209951857)
                    ·
                      refine ⟨3504339099203845657463893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4672452132271794209951857 3504339099203845657463893)
                      ·
                        rfl

theorem cell23_6824676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 2, 1, 2, 2].length) (baseStart_6824676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824676 prefixEnd_6824676 := by exact prefixLift 6824676
  have htrace : WordTrace (prefixWord ++ tailWord_6824676) baseStart_6824676 baseEnd_6824676 := by
    simpa [prefixWord, tailWord_6824676, baseEnd_6824676] using wordTrace_append hprefix tailTrace_6824676
  have hstable : (prefixWord ++ tailWord_6824676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824676).length < 2 ^ (prefixWord ++ tailWord_6824676).sum := by decide
  have hdescent : baseEnd_6824676 < baseStart_6824676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824691 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 1, 8]
def baseStart_6824691 : Nat := 118140960795 + 6824691 * 2 ^ 59
def prefixEnd_6824691 : Nat := 4983230072969 + 3 ^ 40 * 6824691 * 2
def baseEnd_6824691 : Nat := 1168115600471221032925441

theorem tailTrace_6824691 : CollatzResearch.WordTrace tailWord_6824691 prefixEnd_6824691 1168115600471221032925441 := by
  unfold tailWord_6824691
  simp only [CollatzResearch.WordTrace]
  refine ⟨248916930118317546272585927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165944620078878364181723951 248916930118317546272585927)
  ·
    refine ⟨373375395177476319408878891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248916930118317546272585927 373375395177476319408878891)
    ·
      refine ⟨560063092766214479113318337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373375395177476319408878891 560063092766214479113318337)
      ·
        refine ⟨420047319574660859334988753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 560063092766214479113318337 420047319574660859334988753)
        ·
          refine ⟨315035489680995644501241565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420047319574660859334988753 315035489680995644501241565)
          ·
            refine ⟨118138308630373366687965587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 315035489680995644501241565 118138308630373366687965587)
            ·
              refine ⟨177207462945560050031948381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118138308630373366687965587 177207462945560050031948381)
              ·
                refine ⟨66452798604585018761980643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177207462945560050031948381 66452798604585018761980643)
                ·
                  refine ⟨99679197906877528142970965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66452798604585018761980643 99679197906877528142970965)
                  ·
                    refine ⟨1168115600471221032925441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 99679197906877528142970965 1168115600471221032925441)
                    ·
                      rfl

theorem cell23_6824691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 8].length) (baseStart_6824691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824691 prefixEnd_6824691 := by exact prefixLift 6824691
  have htrace : WordTrace (prefixWord ++ tailWord_6824691) baseStart_6824691 baseEnd_6824691 := by
    simpa [prefixWord, tailWord_6824691, baseEnd_6824691] using wordTrace_append hprefix tailTrace_6824691
  have hstable : (prefixWord ++ tailWord_6824691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824691).length < 2 ^ (prefixWord ++ tailWord_6824691).sum := by decide
  have hdescent : baseEnd_6824691 < baseStart_6824691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824693 : List Nat := [1, 3, 6, 1, 2, 1, 1, 2, 1, 1, 4]
def baseStart_6824693 : Nat := 118140960795 + 6824693 * 2 ^ 59
def prefixEnd_6824693 : Nat := 4983230072969 + 3 ^ 40 * 6824693 * 2
def baseEnd_6824693 : Nat := 3504347828374972090951315

theorem tailTrace_6824693 : CollatzResearch.WordTrace tailWord_6824693 prefixEnd_6824693 3504347828374972090951315 := by
  unfold tailWord_6824693
  simp only [CollatzResearch.WordTrace]
  refine ⟨248917003064310300614158733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165944668709540200409439155 248917003064310300614158733)
  ·
    refine ⟨93343876149116362730309525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248917003064310300614158733 93343876149116362730309525)
    ·
      refine ⟨4375494194489829502983259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 93343876149116362730309525 4375494194489829502983259)
      ·
        refine ⟨6563241291734744254474889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4375494194489829502983259 6563241291734744254474889)
        ·
          refine ⟨4922430968801058190856167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6563241291734744254474889 4922430968801058190856167)
          ·
            refine ⟨7383646453201587286284251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4922430968801058190856167 7383646453201587286284251)
            ·
              refine ⟨11075469679802380929426377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7383646453201587286284251 11075469679802380929426377)
              ·
                refine ⟨8306602259851785697069783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11075469679802380929426377 8306602259851785697069783)
                ·
                  refine ⟨12459903389777678545604675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8306602259851785697069783 12459903389777678545604675)
                  ·
                    refine ⟨18689855084666517818407013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12459903389777678545604675 18689855084666517818407013)
                    ·
                      refine ⟨3504347828374972090951315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18689855084666517818407013 3504347828374972090951315)
                      ·
                        rfl

theorem cell23_6824693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_6824693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824693 prefixEnd_6824693 := by exact prefixLift 6824693
  have htrace : WordTrace (prefixWord ++ tailWord_6824693) baseStart_6824693 baseEnd_6824693 := by
    simpa [prefixWord, tailWord_6824693, baseEnd_6824693] using wordTrace_append hprefix tailTrace_6824693
  have hstable : (prefixWord ++ tailWord_6824693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824693).length < 2 ^ (prefixWord ++ tailWord_6824693).sum := by decide
  have hdescent : baseEnd_6824693 < baseStart_6824693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824728 : List Nat := [2, 1, 2, 3, 1, 1, 1, 4, 2, 2, 4]
def baseStart_6824728 : Nat := 118140960795 + 6824728 * 2 ^ 59
def prefixEnd_6824728 : Nat := 4983230072969 + 3 ^ 40 * 6824728 * 2
def baseEnd_6824728 : Nat := 3504365800197879454013653

theorem tailTrace_6824728 : CollatzResearch.WordTrace tailWord_6824728 prefixEnd_6824728 3504365800197879454013653 := by
  unfold tailWord_6824728
  simp only [CollatzResearch.WordTrace]
  refine ⟨124459139809591750795841419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165945519746122334394455225 124459139809591750795841419)
  ·
    refine ⟨186688709714387626193762129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124459139809591750795841419 186688709714387626193762129)
    ·
      refine ⟨140016532285790719645321597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186688709714387626193762129 140016532285790719645321597)
      ·
        refine ⟨52506199607171519866995599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140016532285790719645321597 52506199607171519866995599)
        ·
          refine ⟨78759299410757279800493399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52506199607171519866995599 78759299410757279800493399)
          ·
            refine ⟨118138949116135919700740099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78759299410757279800493399 118138949116135919700740099)
            ·
              refine ⟨177208423674203879551110149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118138949116135919700740099 177208423674203879551110149)
              ·
                refine ⟨33226579438913227415833153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177208423674203879551110149 33226579438913227415833153)
                ·
                  refine ⟨24919934579184920561874865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33226579438913227415833153 24919934579184920561874865)
                  ·
                    refine ⟨18689950934388690421406149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24919934579184920561874865 18689950934388690421406149)
                    ·
                      refine ⟨3504365800197879454013653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18689950934388690421406149 3504365800197879454013653)
                      ·
                        rfl

theorem cell23_6824728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_6824728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824728 prefixEnd_6824728 := by exact prefixLift 6824728
  have htrace : WordTrace (prefixWord ++ tailWord_6824728) baseStart_6824728 baseEnd_6824728 := by
    simpa [prefixWord, tailWord_6824728, baseEnd_6824728] using wordTrace_append hprefix tailTrace_6824728
  have hstable : (prefixWord ++ tailWord_6824728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824728).length < 2 ^ (prefixWord ++ tailWord_6824728).sum := by decide
  have hdescent : baseEnd_6824728 < baseStart_6824728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824778 : List Nat := [3, 1, 2, 1, 1, 1, 2, 4, 1, 2, 5]
def baseStart_6824778 : Nat := 118140960795 + 6824778 * 2 ^ 59
def prefixEnd_6824778 : Nat := 4983230072969 + 3 ^ 40 * 6824778 * 2
def baseEnd_6824778 : Nat := 3504391474230604258388423

theorem tailTrace_6824778 : CollatzResearch.WordTrace tailWord_6824778 prefixEnd_6824778 3504391474230604258388423 := by
  unfold tailWord_6824778
  simp only [CollatzResearch.WordTrace]
  refine ⟨62230025817250590032750747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165946735512668240087335325 62230025817250590032750747)
  ·
    refine ⟨93345038725875885049126121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62230025817250590032750747 93345038725875885049126121)
    ·
      refine ⟨70008779044406913786844591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93345038725875885049126121 70008779044406913786844591)
      ·
        refine ⟨105013168566610370680266887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70008779044406913786844591 105013168566610370680266887)
        ·
          refine ⟨157519752849915556020400331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105013168566610370680266887 157519752849915556020400331)
          ·
            refine ⟨236279629274873334030600497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157519752849915556020400331 236279629274873334030600497)
            ·
              refine ⟨177209721956155000522950373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236279629274873334030600497 177209721956155000522950373)
              ·
                refine ⟨33226822866779062598053195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177209721956155000522950373 33226822866779062598053195)
                ·
                  refine ⟨49840234300168593897079793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33226822866779062598053195 49840234300168593897079793)
                  ·
                    refine ⟨37380175725126445422809845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49840234300168593897079793 37380175725126445422809845)
                    ·
                      refine ⟨3504391474230604258388423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37380175725126445422809845 3504391474230604258388423)
                      ·
                        rfl

theorem cell23_6824778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_6824778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824778 prefixEnd_6824778 := by exact prefixLift 6824778
  have htrace : WordTrace (prefixWord ++ tailWord_6824778) baseStart_6824778 baseEnd_6824778 := by
    simpa [prefixWord, tailWord_6824778, baseEnd_6824778] using wordTrace_append hprefix tailTrace_6824778
  have hstable : (prefixWord ++ tailWord_6824778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824778).length < 2 ^ (prefixWord ++ tailWord_6824778).sum := by decide
  have hdescent : baseEnd_6824778 < baseStart_6824778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824822 : List Nat := [5, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4]
def baseStart_6824822 : Nat := 118140960795 + 6824822 * 2 ^ 59
def prefixEnd_6824822 : Nat := 4983230072969 + 3 ^ 40 * 6824822 * 2
def baseEnd_6824822 : Nat := 3504414067379402086238221

theorem tailTrace_6824822 : CollatzResearch.WordTrace tailWord_6824822 prefixEnd_6824822 3504414067379402086238221 := by
  unfold tailWord_6824822
  simp only [CollatzResearch.WordTrace]
  refine ⟨15557606755052684727850295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165947805387228637097069813 15557606755052684727850295)
  ·
    refine ⟨23336410132579027091775443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15557606755052684727850295 23336410132579027091775443)
    ·
      refine ⟨35004615198868540637663165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23336410132579027091775443 35004615198868540637663165)
      ·
        refine ⟨13126730699575702739123687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35004615198868540637663165 13126730699575702739123687)
        ·
          refine ⟨19690096049363554108685531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13126730699575702739123687 19690096049363554108685531)
          ·
            refine ⟨29535144074045331163028297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19690096049363554108685531 29535144074045331163028297)
            ·
              refine ⟨22151358055533998372271223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29535144074045331163028297 22151358055533998372271223)
              ·
                refine ⟨33227037083300997558406835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22151358055533998372271223 33227037083300997558406835)
                ·
                  refine ⟨49840555624951496337610253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33227037083300997558406835 49840555624951496337610253)
                  ·
                    refine ⟨18690208359356811126603845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49840555624951496337610253 18690208359356811126603845)
                    ·
                      refine ⟨3504414067379402086238221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18690208359356811126603845 3504414067379402086238221)
                      ·
                        rfl

theorem cell23_6824822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_6824822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824822 prefixEnd_6824822 := by exact prefixLift 6824822
  have htrace : WordTrace (prefixWord ++ tailWord_6824822) baseStart_6824822 baseEnd_6824822 := by
    simpa [prefixWord, tailWord_6824822, baseEnd_6824822] using wordTrace_append hprefix tailTrace_6824822
  have hstable : (prefixWord ++ tailWord_6824822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824822).length < 2 ^ (prefixWord ++ tailWord_6824822).sum := by decide
  have hdescent : baseEnd_6824822 < baseStart_6824822 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824825 : List Nat := [1, 2, 1, 3, 2, 3, 2, 1, 1, 4, 3]
def baseStart_6824825 : Nat := 118140960795 + 6824825 * 2 ^ 59
def prefixEnd_6824825 : Nat := 4983230072969 + 3 ^ 40 * 6824825 * 2
def baseEnd_6824825 : Nat := 3504415607821365574500707

theorem tailTrace_6824825 : CollatzResearch.WordTrace tailWord_6824825 prefixEnd_6824825 3504415607821365574500707 := by
  unfold tailWord_6824825
  simp only [CollatzResearch.WordTrace]
  refine ⟨248921817499832087157963929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165947878333221391438642619 248921817499832087157963929)
  ·
    refine ⟨186691363124874065368472947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248921817499832087157963929 186691363124874065368472947)
    ·
      refine ⟨280037044687311098052709421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186691363124874065368472947 280037044687311098052709421)
      ·
        refine ⟨105013891757741661769766033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280037044687311098052709421 105013891757741661769766033)
        ·
          refine ⟨78760418818306246327324525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105013891757741661769766033 78760418818306246327324525)
          ·
            refine ⟨29535157056864842372746697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78760418818306246327324525 29535157056864842372746697)
            ·
              refine ⟨22151367792648631779560023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29535157056864842372746697 22151367792648631779560023)
              ·
                refine ⟨33227051688972947669340035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22151367792648631779560023 33227051688972947669340035)
                ·
                  refine ⟨49840577533459421504010053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33227051688972947669340035 49840577533459421504010053)
                  ·
                    refine ⟨9345108287523641532001885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49840577533459421504010053 9345108287523641532001885)
                    ·
                      refine ⟨3504415607821365574500707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9345108287523641532001885 3504415607821365574500707)
                      ·
                        rfl

theorem cell23_6824825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_6824825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824825 prefixEnd_6824825 := by exact prefixLift 6824825
  have htrace : WordTrace (prefixWord ++ tailWord_6824825) baseStart_6824825 baseEnd_6824825 := by
    simpa [prefixWord, tailWord_6824825, baseEnd_6824825] using wordTrace_append hprefix tailTrace_6824825
  have hstable : (prefixWord ++ tailWord_6824825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824825).length < 2 ^ (prefixWord ++ tailWord_6824825).sum := by decide
  have hdescent : baseEnd_6824825 < baseStart_6824825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824832 : List Nat := [2, 1, 1, 2, 1, 2, 2, 7, 1, 4]
def baseStart_6824832 : Nat := 118140960795 + 6824832 * 2 ^ 59
def prefixEnd_6824832 : Nat := 4983230072969 + 3 ^ 40 * 6824832 * 2
def baseEnd_6824832 : Nat := 1168139734061982349037725

theorem tailTrace_6824832 : CollatzResearch.WordTrace tailWord_6824832 prefixEnd_6824832 1168139734061982349037725 := by
  unfold tailWord_6824832
  simp only [CollatzResearch.WordTrace]
  refine ⟨124461036405403363676734375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165948048540537818235645833 124461036405403363676734375)
  ·
    refine ⟨186691554608105045515101563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124461036405403363676734375 186691554608105045515101563)
    ·
      refine ⟨280037331912157568272652345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186691554608105045515101563 280037331912157568272652345)
      ·
        refine ⟨210027998934118176204489259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280037331912157568272652345 210027998934118176204489259)
        ·
          refine ⟨315041998401177264306733889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210027998934118176204489259 315041998401177264306733889)
          ·
            refine ⟨236281498800882948230050417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315041998401177264306733889 236281498800882948230050417)
            ·
              refine ⟨177211124100662211172537813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236281498800882948230050417 177211124100662211172537813)
              ·
                refine ⟨4153385721109270574356355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 177211124100662211172537813 4153385721109270574356355)
                ·
                  refine ⟨6230078581663905861534533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4153385721109270574356355 6230078581663905861534533)
                  ·
                    refine ⟨1168139734061982349037725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6230078581663905861534533 1168139734061982349037725)
                    ·
                      rfl

theorem cell23_6824832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 7, 1, 4].length) (baseStart_6824832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824832 prefixEnd_6824832 := by exact prefixLift 6824832
  have htrace : WordTrace (prefixWord ++ tailWord_6824832) baseStart_6824832 baseEnd_6824832 := by
    simpa [prefixWord, tailWord_6824832, baseEnd_6824832] using wordTrace_append hprefix tailTrace_6824832
  have hstable : (prefixWord ++ tailWord_6824832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824832).length < 2 ^ (prefixWord ++ tailWord_6824832).sum := by decide
  have hdescent : baseEnd_6824832 < baseStart_6824832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824842 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 4, 2, 3]
def baseStart_6824842 : Nat := 118140960795 + 6824842 * 2 ^ 59
def prefixEnd_6824842 : Nat := 4983230072969 + 3 ^ 40 * 6824842 * 2
def baseEnd_6824842 : Nat := 3504424336992492007988129

theorem tailTrace_6824842 : CollatzResearch.WordTrace tailWord_6824842 prefixEnd_6824842 3504424336992492007988129 := by
  unfold tailWord_6824842
  simp only [CollatzResearch.WordTrace]
  refine ⟨62230609385192624765333195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165948291693846999374221853 62230609385192624765333195)
  ·
    refine ⟨93345914077788937147999793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62230609385192624765333195 93345914077788937147999793)
    ·
      refine ⟨70009435558341702860999845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93345914077788937147999793 70009435558341702860999845)
      ·
        refine ⟨13126769167189069286437471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70009435558341702860999845 13126769167189069286437471)
        ·
          refine ⟨19690153750783603929656207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13126769167189069286437471 19690153750783603929656207)
          ·
            refine ⟨29535230626175405894484311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19690153750783603929656207 29535230626175405894484311)
            ·
              refine ⟨44302845939263108841726467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29535230626175405894484311 44302845939263108841726467)
              ·
                refine ⟨66454268908894663262589701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44302845939263108841726467 66454268908894663262589701)
                ·
                  refine ⟨12460175420417749361735569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66454268908894663262589701 12460175420417749361735569)
                  ·
                    refine ⟨9345131565313312021301677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12460175420417749361735569 9345131565313312021301677)
                    ·
                      refine ⟨3504424336992492007988129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9345131565313312021301677 3504424336992492007988129)
                      ·
                        rfl

theorem cell23_6824842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_6824842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824842 prefixEnd_6824842 := by exact prefixLift 6824842
  have htrace : WordTrace (prefixWord ++ tailWord_6824842) baseStart_6824842 baseEnd_6824842 := by
    simpa [prefixWord, tailWord_6824842, baseEnd_6824842] using wordTrace_append hprefix tailTrace_6824842
  have hstable : (prefixWord ++ tailWord_6824842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824842).length < 2 ^ (prefixWord ++ tailWord_6824842).sum := by decide
  have hdescent : baseEnd_6824842 < baseStart_6824842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824900 : List Nat := [2, 3, 3, 3, 1, 2, 2, 2, 1, 4]
def baseStart_6824900 : Nat := 118140960795 + 6824900 * 2 ^ 59
def prefixEnd_6824900 : Nat := 4983230072969 + 3 ^ 40 * 6824900 * 2
def baseEnd_6824900 : Nat := 1168151372956817593687621

theorem tailTrace_6824900 : CollatzResearch.WordTrace tailWord_6824900 prefixEnd_6824900 1168151372956817593687621 := by
  unfold tailWord_6824900
  simp only [CollatzResearch.WordTrace]
  refine ⟨124462276487280187483472077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165949701983040249977962769 124462276487280187483472077)
  ·
    refine ⟨46673353682730070306302029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124462276487280187483472077 46673353682730070306302029)
    ·
      refine ⟨17502507631023776364863261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46673353682730070306302029 17502507631023776364863261)
      ·
        refine ⟨6563440361633916136823723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17502507631023776364863261 6563440361633916136823723)
        ·
          refine ⟨9845160542450874205235585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6563440361633916136823723 9845160542450874205235585)
          ·
            refine ⟨7383870406838155653926689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9845160542450874205235585 7383870406838155653926689)
            ·
              refine ⟨5537902805128616740445017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7383870406838155653926689 5537902805128616740445017)
              ·
                refine ⟨4153427103846462555333763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5537902805128616740445017 4153427103846462555333763)
                ·
                  refine ⟨6230140655769693833000645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4153427103846462555333763 6230140655769693833000645)
                  ·
                    refine ⟨1168151372956817593687621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6230140655769693833000645 1168151372956817593687621)
                    ·
                      rfl

theorem cell23_6824900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_6824900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824900 prefixEnd_6824900 := by exact prefixLift 6824900
  have htrace : WordTrace (prefixWord ++ tailWord_6824900) baseStart_6824900 baseEnd_6824900 := by
    simpa [prefixWord, tailWord_6824900, baseEnd_6824900] using wordTrace_append hprefix tailTrace_6824900
  have hstable : (prefixWord ++ tailWord_6824900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824900).length < 2 ^ (prefixWord ++ tailWord_6824900).sum := by decide
  have hdescent : baseEnd_6824900 < baseStart_6824900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824922 : List Nat := [3, 1, 1, 2, 4, 2, 2, 1, 1, 6]
def baseStart_6824922 : Nat := 118140960795 + 6824922 * 2 ^ 59
def prefixEnd_6824922 : Nat := 4983230072969 + 3 ^ 40 * 6824922 * 2
def baseEnd_6824922 : Nat := 1168155138481617231662587

theorem tailTrace_6824922 : CollatzResearch.WordTrace tailWord_6824922 prefixEnd_6824922 1168155138481617231662587 := by
  unfold tailWord_6824922
  simp only [CollatzResearch.WordTrace]
  refine ⟨62231338845120168181061255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165950236920320448482830013 62231338845120168181061255)
  ·
    refine ⟨93347008267680252271591883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62231338845120168181061255 93347008267680252271591883)
    ·
      refine ⟨140020512401520378407387825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93347008267680252271591883 140020512401520378407387825)
      ·
        refine ⟨105015384301140283805540869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140020512401520378407387825 105015384301140283805540869)
        ·
          refine ⟨19690384556463803213538913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105015384301140283805540869 19690384556463803213538913)
          ·
            refine ⟨14767788417347852410154185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19690384556463803213538913 14767788417347852410154185)
            ·
              refine ⟨11075841313010889307615639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14767788417347852410154185 11075841313010889307615639)
              ·
                refine ⟨16613761969516333961423459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11075841313010889307615639 16613761969516333961423459)
                ·
                  refine ⟨24920642954274500942135189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16613761969516333961423459 24920642954274500942135189)
                  ·
                    refine ⟨1168155138481617231662587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24920642954274500942135189 1168155138481617231662587)
                    ·
                      rfl

theorem cell23_6824922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 1, 6].length) (baseStart_6824922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824922 prefixEnd_6824922 := by exact prefixLift 6824922
  have htrace : WordTrace (prefixWord ++ tailWord_6824922) baseStart_6824922 baseEnd_6824922 := by
    simpa [prefixWord, tailWord_6824922, baseEnd_6824922] using wordTrace_append hprefix tailTrace_6824922
  have hstable : (prefixWord ++ tailWord_6824922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824922).length < 2 ^ (prefixWord ++ tailWord_6824922).sum := by decide
  have hdescent : baseEnd_6824922 < baseStart_6824922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824933 : List Nat := [1, 3, 1, 6, 1, 2, 1, 1, 2, 3, 2]
def baseStart_6824933 : Nat := 118140960795 + 6824933 * 2 ^ 59
def prefixEnd_6824933 : Nat := 4983230072969 + 3 ^ 40 * 6824933 * 2
def baseEnd_6824933 : Nat := 3504471063732051151950211

theorem tailTrace_6824933 : CollatzResearch.WordTrace tailWord_6824933 prefixEnd_6824933 3504471063732051151950211 := by
  unfold tailWord_6824933
  simp only [CollatzResearch.WordTrace]
  refine ⟨248925756583440821602895453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165950504388960547735263635 248925756583440821602895453)
  ·
    refine ⟨93347158718790308101085795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248925756583440821602895453 93347158718790308101085795)
    ·
      refine ⟨140020738078185462151628693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93347158718790308101085795 140020738078185462151628693)
      ·
        refine ⟨6563472097414943538357595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 140020738078185462151628693 6563472097414943538357595)
        ·
          refine ⟨9845208146122415307536393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6563472097414943538357595 9845208146122415307536393)
          ·
            refine ⟨7383906109591811480652295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9845208146122415307536393 7383906109591811480652295)
            ·
              refine ⟨11075859164387717220978443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7383906109591811480652295 11075859164387717220978443)
              ·
                refine ⟨16613788746581575831467665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11075859164387717220978443 16613788746581575831467665)
                ·
                  refine ⟨12460341559936181873600749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16613788746581575831467665 12460341559936181873600749)
                  ·
                    refine ⟨4672628084976068202600281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12460341559936181873600749 4672628084976068202600281)
                    ·
                      refine ⟨3504471063732051151950211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4672628084976068202600281 3504471063732051151950211)
                      ·
                        rfl

theorem cell23_6824933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_6824933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824933 prefixEnd_6824933 := by exact prefixLift 6824933
  have htrace : WordTrace (prefixWord ++ tailWord_6824933) baseStart_6824933 baseEnd_6824933 := by
    simpa [prefixWord, tailWord_6824933, baseEnd_6824933] using wordTrace_append hprefix tailTrace_6824933
  have hstable : (prefixWord ++ tailWord_6824933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824933).length < 2 ^ (prefixWord ++ tailWord_6824933).sum := by decide
  have hdescent : baseEnd_6824933 < baseStart_6824933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824946 : List Nat := [3, 2, 1, 5, 1, 1, 1, 3, 1, 1, 4]
def baseStart_6824946 : Nat := 118140960795 + 6824946 * 2 ^ 59
def prefixEnd_6824946 : Nat := 4983230072969 + 3 ^ 40 * 6824946 * 2
def baseEnd_6824946 : Nat := 3504477738980559601087651

theorem tailTrace_6824946 : CollatzResearch.WordTrace tailWord_6824946 prefixEnd_6824946 3504477738980559601087651 := by
  unfold tailWord_6824946
  simp only [CollatzResearch.WordTrace]
  refine ⟨62231557683098431205779673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165950820488262483215412461 62231557683098431205779673)
  ·
    refine ⟨46673668262323823404334755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62231557683098431205779673 46673668262323823404334755)
    ·
      refine ⟨70010502393485735106502133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46673668262323823404334755 70010502393485735106502133)
      ·
        refine ⟨6563484599389287666234575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70010502393485735106502133 6563484599389287666234575)
        ·
          refine ⟨9845226899083931499351863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6563484599389287666234575 9845226899083931499351863)
          ·
            refine ⟨14767840348625897249027795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9845226899083931499351863 14767840348625897249027795)
            ·
              refine ⟨22151760522938845873541693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14767840348625897249027795 22151760522938845873541693)
              ·
                refine ⟨8306910196102067202578135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22151760522938845873541693 8306910196102067202578135)
                ·
                  refine ⟨12460365294153100803867203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8306910196102067202578135 12460365294153100803867203)
                  ·
                    refine ⟨18690547941229651205800805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12460365294153100803867203 18690547941229651205800805)
                    ·
                      refine ⟨3504477738980559601087651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18690547941229651205800805 3504477738980559601087651)
                      ·
                        rfl

theorem cell23_6824946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_6824946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824946 prefixEnd_6824946 := by exact prefixLift 6824946
  have htrace : WordTrace (prefixWord ++ tailWord_6824946) baseStart_6824946 baseEnd_6824946 := by
    simpa [prefixWord, tailWord_6824946, baseEnd_6824946] using wordTrace_append hprefix tailTrace_6824946
  have hstable : (prefixWord ++ tailWord_6824946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824946).length < 2 ^ (prefixWord ++ tailWord_6824946).sum := by decide
  have hdescent : baseEnd_6824946 < baseStart_6824946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6824985 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 2, 3, 4]
def baseStart_6824985 : Nat := 118140960795 + 6824985 * 2 ^ 59
def prefixEnd_6824985 : Nat := 4983230072969 + 3 ^ 40 * 6824985 * 2
def baseEnd_6824985 : Nat := 3504497764726084948499971

theorem tailTrace_6824985 : CollatzResearch.WordTrace tailWord_6824985 prefixEnd_6824985 3504497764726084948499971 := by
  unfold tailWord_6824985
  simp only [CollatzResearch.WordTrace]
  refine ⟨248927653179252434483788409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165951768786168289655858939 248927653179252434483788409)
  ·
    refine ⟨186695739884439325862841307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248927653179252434483788409 186695739884439325862841307)
    ·
      refine ⟨280043609826658988794261961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186695739884439325862841307 280043609826658988794261961)
      ·
        refine ⟨210032707369994241595696471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280043609826658988794261961 210032707369994241595696471)
        ·
          refine ⟨315049061054991362393544707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210032707369994241595696471 315049061054991362393544707)
          ·
            refine ⟨472573591582487043590317061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315049061054991362393544707 472573591582487043590317061)
            ·
              refine ⟨88607548421716320673184449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 472573591582487043590317061 88607548421716320673184449)
              ·
                refine ⟨66455661316287240504888337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88607548421716320673184449 66455661316287240504888337)
                ·
                  refine ⟨49841745987215430378666253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66455661316287240504888337 49841745987215430378666253)
                  ·
                    refine ⟨18690654745205786391999845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49841745987215430378666253 18690654745205786391999845)
                    ·
                      refine ⟨3504497764726084948499971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18690654745205786391999845 3504497764726084948499971)
                      ·
                        rfl

theorem cell23_6824985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_6824985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6824985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6824985 prefixEnd_6824985 := by exact prefixLift 6824985
  have htrace : WordTrace (prefixWord ++ tailWord_6824985) baseStart_6824985 baseEnd_6824985 := by
    simpa [prefixWord, tailWord_6824985, baseEnd_6824985] using wordTrace_append hprefix tailTrace_6824985
  have hstable : (prefixWord ++ tailWord_6824985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6824985).length < 2 ^ (prefixWord ++ tailWord_6824985).sum := by decide
  have hdescent : baseEnd_6824985 < baseStart_6824985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6824985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825006 : List Nat := [4, 1, 3, 1, 1, 1, 1, 5, 1, 3, 2]
def baseStart_6825006 : Nat := 118140960795 + 6825006 * 2 ^ 59
def prefixEnd_6825006 : Nat := 4983230072969 + 3 ^ 40 * 6825006 * 2
def baseEnd_6825006 : Nat := 3504508547819829366337375

theorem tailTrace_6825006 : CollatzResearch.WordTrace tailWord_6825006 prefixEnd_6825006 3504508547819829366337375 := by
  unfold tailWord_6825006
  simp only [CollatzResearch.WordTrace]
  refine ⟨31116052389022044383787859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165952279408117570046868581 31116052389022044383787859)
  ·
    refine ⟨46674078583533066575681789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31116052389022044383787859 46674078583533066575681789)
    ·
      refine ⟨17502779468824899965880671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46674078583533066575681789 17502779468824899965880671)
      ·
        refine ⟨26254169203237349948821007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17502779468824899965880671 26254169203237349948821007)
        ·
          refine ⟨39381253804856024923231511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26254169203237349948821007 39381253804856024923231511)
          ·
            refine ⟨59071880707284037384847267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39381253804856024923231511 59071880707284037384847267)
            ·
              refine ⟨88607821060926056077270901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59071880707284037384847267 88607821060926056077270901)
              ·
                refine ⟨8306983224461817757244147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88607821060926056077270901 8306983224461817757244147)
                ·
                  refine ⟨12460474836692726635866221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8306983224461817757244147 12460474836692726635866221)
                  ·
                    refine ⟨4672678063759772488449833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12460474836692726635866221 4672678063759772488449833)
                    ·
                      refine ⟨3504508547819829366337375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4672678063759772488449833 3504508547819829366337375)
                      ·
                        rfl

theorem cell23_6825006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_6825006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825006 prefixEnd_6825006 := by exact prefixLift 6825006
  have htrace : WordTrace (prefixWord ++ tailWord_6825006) baseStart_6825006 baseEnd_6825006 := by
    simpa [prefixWord, tailWord_6825006, baseEnd_6825006] using wordTrace_append hprefix tailTrace_6825006
  have hstable : (prefixWord ++ tailWord_6825006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825006).length < 2 ^ (prefixWord ++ tailWord_6825006).sum := by decide
  have hdescent : baseEnd_6825006 < baseStart_6825006 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825030 : List Nat := [6, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3]
def baseStart_6825030 : Nat := 118140960795 + 6825030 * 2 ^ 59
def prefixEnd_6825030 : Nat := 4983230072969 + 3 ^ 40 * 6825030 * 2
def baseEnd_6825030 : Nat := 3504520871355537272437265

theorem tailTrace_6825030 : CollatzResearch.WordTrace tailWord_6825030 prefixEnd_6825030 3504520871355537272437265 := by
  unfold tailWord_6825030
  simp only [CollatzResearch.WordTrace]
  refine ⟨7779040452002793974036767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 165952862976059604779451029 7779040452002793974036767)
  ·
    refine ⟨11668560678004190961055151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7779040452002793974036767 11668560678004190961055151)
    ·
      refine ⟨17502841017006286441582727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11668560678004190961055151 17502841017006286441582727)
      ·
        refine ⟨26254261525509429662374091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17502841017006286441582727 26254261525509429662374091)
        ·
          refine ⟨39381392288264144493561137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26254261525509429662374091 39381392288264144493561137)
          ·
            refine ⟨29536044216198108370170853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39381392288264144493561137 29536044216198108370170853)
            ·
              refine ⟨5538008290537145319407035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29536044216198108370170853 5538008290537145319407035)
              ·
                refine ⟨8307012435805717979110553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5538008290537145319407035 8307012435805717979110553)
                ·
                  refine ⟨6230259326854288484332915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8307012435805717979110553 6230259326854288484332915)
                  ·
                    refine ⟨9345388990281432726499373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6230259326854288484332915 9345388990281432726499373)
                    ·
                      refine ⟨3504520871355537272437265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9345388990281432726499373 3504520871355537272437265)
                      ·
                        rfl

theorem cell23_6825030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_6825030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825030 prefixEnd_6825030 := by exact prefixLift 6825030
  have htrace : WordTrace (prefixWord ++ tailWord_6825030) baseStart_6825030 baseEnd_6825030 := by
    simpa [prefixWord, tailWord_6825030, baseEnd_6825030] using wordTrace_append hprefix tailTrace_6825030
  have hstable : (prefixWord ++ tailWord_6825030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825030).length < 2 ^ (prefixWord ++ tailWord_6825030).sum := by decide
  have hdescent : baseEnd_6825030 < baseStart_6825030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825053 : List Nat := [1, 4, 4, 1, 2, 1, 1, 2, 1, 4, 2]
def baseStart_6825053 : Nat := 118140960795 + 6825053 * 2 ^ 59
def prefixEnd_6825053 : Nat := 4983230072969 + 3 ^ 40 * 6825053 * 2
def baseEnd_6825053 : Nat := 3504532681410590682449659

theorem tailTrace_6825053 : CollatzResearch.WordTrace tailWord_6825053 prefixEnd_6825053 3504532681410590682449659 := by
  unfold tailWord_6825053
  simp only [CollatzResearch.WordTrace]
  refine ⟨248930133343006082097263813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165953422228670721398175875 248930133343006082097263813)
  ·
    refine ⟨46674400001813640393236965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248930133343006082097263813 46674400001813640393236965)
    ·
      refine ⟨8751450000340057573731931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46674400001813640393236965 8751450000340057573731931)
      ·
        refine ⟨13127175000510086360597897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8751450000340057573731931 13127175000510086360597897)
        ·
          refine ⟨9845381250382564770448423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13127175000510086360597897 9845381250382564770448423)
          ·
            refine ⟨14768071875573847155672635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9845381250382564770448423 14768071875573847155672635)
            ·
              refine ⟨22152107813360770733508953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14768071875573847155672635 22152107813360770733508953)
              ·
                refine ⟨16614080860020578050131715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22152107813360770733508953 16614080860020578050131715)
                ·
                  refine ⟨24921121290030867075197573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16614080860020578050131715 24921121290030867075197573)
                  ·
                    refine ⟨4672710241880787576599545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24921121290030867075197573 4672710241880787576599545)
                    ·
                      refine ⟨3504532681410590682449659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4672710241880787576599545 3504532681410590682449659)
                      ·
                        rfl

theorem cell23_6825053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_6825053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825053 prefixEnd_6825053 := by exact prefixLift 6825053
  have htrace : WordTrace (prefixWord ++ tailWord_6825053) baseStart_6825053 baseEnd_6825053 := by
    simpa [prefixWord, tailWord_6825053, baseEnd_6825053] using wordTrace_append hprefix tailTrace_6825053
  have hstable : (prefixWord ++ tailWord_6825053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825053).length < 2 ^ (prefixWord ++ tailWord_6825053).sum := by decide
  have hdescent : baseEnd_6825053 < baseStart_6825053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825072 : List Nat := [2, 1, 1, 1, 5, 1, 1, 4, 2, 5]
def baseStart_6825072 : Nat := 118140960795 + 6825072 * 2 ^ 59
def prefixEnd_6825072 : Nat := 4983230072969 + 3 ^ 40 * 6825072 * 2
def baseEnd_6825072 : Nat := 1168180812514342036037357

theorem tailTrace_6825072 : CollatzResearch.WordTrace tailWord_6825072 prefixEnd_6825072 1168180812514342036037357 := by
  unfold tailWord_6825072
  simp only [CollatzResearch.WordTrace]
  refine ⟨124465413164968624171102735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165953884219958165561470313 124465413164968624171102735)
  ·
    refine ⟨186698119747452936256654103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124465413164968624171102735 186698119747452936256654103)
    ·
      refine ⟨280047179621179404384981155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186698119747452936256654103 280047179621179404384981155)
      ·
        refine ⟨420070769431769106577471733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280047179621179404384981155 420070769431769106577471733)
        ·
          refine ⟨39381634634228353741637975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 420070769431769106577471733 39381634634228353741637975)
          ·
            refine ⟨59072451951342530612456963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39381634634228353741637975 59072451951342530612456963)
            ·
              refine ⟨88608677927013795918685445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59072451951342530612456963 88608677927013795918685445)
              ·
                refine ⟨16614127111315086734753521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88608677927013795918685445 16614127111315086734753521)
                ·
                  refine ⟨12460595333486315051065141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16614127111315086734753521 12460595333486315051065141)
                  ·
                    refine ⟨1168180812514342036037357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12460595333486315051065141 1168180812514342036037357)
                    ·
                      rfl

theorem cell23_6825072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 2, 5].length) (baseStart_6825072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825072 prefixEnd_6825072 := by exact prefixLift 6825072
  have htrace : WordTrace (prefixWord ++ tailWord_6825072) baseStart_6825072 baseEnd_6825072 := by
    simpa [prefixWord, tailWord_6825072, baseEnd_6825072] using wordTrace_append hprefix tailTrace_6825072
  have hstable : (prefixWord ++ tailWord_6825072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825072).length < 2 ^ (prefixWord ++ tailWord_6825072).sum := by decide
  have hdescent : baseEnd_6825072 < baseStart_6825072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825106 : List Nat := [3, 2, 3, 1, 1, 4, 1, 1, 2, 5]
def baseStart_6825106 : Nat := 118140960795 + 6825106 * 2 ^ 59
def prefixEnd_6825106 : Nat := 4983230072969 + 3 ^ 40 * 6825106 * 2
def baseEnd_6825106 : Nat := 1168186631961759658362305

theorem tailTrace_6825106 : CollatzResearch.WordTrace tailWord_6825106 prefixEnd_6825106 1168186631961759658362305 := by
  unfold tailWord_6825106
  simp only [CollatzResearch.WordTrace]
  refine ⟨62233016602953518037235793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165954710941209381432628781 62233016602953518037235793)
  ·
    refine ⟨46674762452215138527926845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62233016602953518037235793 46674762452215138527926845)
    ·
      refine ⟨17503035919580676947972567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46674762452215138527926845 17503035919580676947972567)
      ·
        refine ⟨26254553879371015421958851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17503035919580676947972567 26254553879371015421958851)
        ·
          refine ⟨39381830819056523132938277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26254553879371015421958851 39381830819056523132938277)
          ·
            refine ⟨7384093278573098087425927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39381830819056523132938277 7384093278573098087425927)
            ·
              refine ⟨11076139917859647131138891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7384093278573098087425927 11076139917859647131138891)
              ·
                refine ⟨16614209876789470696708337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11076139917859647131138891 16614209876789470696708337)
                ·
                  refine ⟨12460657407592103022531253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16614209876789470696708337 12460657407592103022531253)
                  ·
                    refine ⟨1168186631961759658362305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12460657407592103022531253 1168186631961759658362305)
                    ·
                      rfl

theorem cell23_6825106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_6825106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825106 prefixEnd_6825106 := by exact prefixLift 6825106
  have htrace : WordTrace (prefixWord ++ tailWord_6825106) baseStart_6825106 baseEnd_6825106 := by
    simpa [prefixWord, tailWord_6825106, baseEnd_6825106] using wordTrace_append hprefix tailTrace_6825106
  have hstable : (prefixWord ++ tailWord_6825106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825106).length < 2 ^ (prefixWord ++ tailWord_6825106).sum := by decide
  have hdescent : baseEnd_6825106 < baseStart_6825106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825132 : List Nat := [2, 2, 1, 1, 1, 1, 1, 8, 6]
def baseStart_6825132 : Nat := 118140960795 + 6825132 * 2 ^ 59
def prefixEnd_6825132 : Nat := 4983230072969 + 3 ^ 40 * 6825132 * 2
def baseEnd_6825132 : Nat := 389397027375810652595755

theorem tailTrace_6825132 : CollatzResearch.WordTrace tailWord_6825132 prefixEnd_6825132 389397027375810652595755 := by
  unfold tailWord_6825132
  simp only [CollatzResearch.WordTrace]
  refine ⟨124466507354859939294694825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165955343139813252392926433 124466507354859939294694825)
  ·
    refine ⟨93349880516144954471021119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124466507354859939294694825 93349880516144954471021119)
    ·
      refine ⟨140024820774217431706531679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93349880516144954471021119 140024820774217431706531679)
      ·
        refine ⟨210037231161326147559797519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140024820774217431706531679 210037231161326147559797519)
        ·
          refine ⟨315055846741989221339696279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210037231161326147559797519 315055846741989221339696279)
          ·
            refine ⟨472583770112983832009544419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315055846741989221339696279 472583770112983832009544419)
            ·
              refine ⟨708875655169475748014316629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472583770112983832009544419 708875655169475748014316629)
              ·
                refine ⟨8307136584017293922042773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 708875655169475748014316629 8307136584017293922042773)
                ·
                  refine ⟨389397027375810652595755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8307136584017293922042773 389397027375810652595755)
                  ·
                    rfl

theorem cell23_6825132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 6].length) (baseStart_6825132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825132 prefixEnd_6825132 := by exact prefixLift 6825132
  have htrace : WordTrace (prefixWord ++ tailWord_6825132) baseStart_6825132 baseEnd_6825132 := by
    simpa [prefixWord, tailWord_6825132, baseEnd_6825132] using wordTrace_append hprefix tailTrace_6825132
  have hstable : (prefixWord ++ tailWord_6825132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825132).length < 2 ^ (prefixWord ++ tailWord_6825132).sum := by decide
  have hdescent : baseEnd_6825132 < baseStart_6825132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825216 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 5, 2, 2]
def baseStart_6825216 : Nat := 118140960795 + 6825216 * 2 ^ 59
def prefixEnd_6825216 : Nat := 4983230072969 + 3 ^ 40 * 6825216 * 2
def baseEnd_6825216 : Nat := 3504616378757273544711409

theorem tailTrace_6825216 : CollatzResearch.WordTrace tailWord_6825216 prefixEnd_6825216 3504616378757273544711409 := by
  unfold tailWord_6825216
  simp only [CollatzResearch.WordTrace]
  refine ⟨124468039220707780467723751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165957385627610373956965001 124468039220707780467723751)
  ·
    refine ⟨186702058831061670701585627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124468039220707780467723751 186702058831061670701585627)
    ·
      refine ⟨280053088246592506052378441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186702058831061670701585627 280053088246592506052378441)
      ·
        refine ⟨210039816184944379539283831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280053088246592506052378441 210039816184944379539283831)
        ·
          refine ⟨315059724277416569308925747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210039816184944379539283831 315059724277416569308925747)
          ·
            refine ⟨472589586416124853963388621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315059724277416569308925747 472589586416124853963388621)
            ·
              refine ⟨177221094906046820236270733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 472589586416124853963388621 177221094906046820236270733)
              ·
                refine ⟨66457910589767557588601525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177221094906046820236270733 66457910589767557588601525)
                ·
                  refine ⟨6230429117790708523931393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66457910589767557588601525 6230429117790708523931393)
                  ·
                    refine ⟨4672821838343031392948545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6230429117790708523931393 4672821838343031392948545)
                    ·
                      refine ⟨3504616378757273544711409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4672821838343031392948545 3504616378757273544711409)
                      ·
                        rfl

theorem cell23_6825216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 5, 2, 2].length) (baseStart_6825216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825216 prefixEnd_6825216 := by exact prefixLift 6825216
  have htrace : WordTrace (prefixWord ++ tailWord_6825216) baseStart_6825216 baseEnd_6825216 := by
    simpa [prefixWord, tailWord_6825216, baseEnd_6825216] using wordTrace_append hprefix tailTrace_6825216
  have hstable : (prefixWord ++ tailWord_6825216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825216).length < 2 ^ (prefixWord ++ tailWord_6825216).sum := by decide
  have hdescent : baseEnd_6825216 < baseStart_6825216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825249 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 5, 3, 3]
def baseStart_6825249 : Nat := 118140960795 + 6825249 * 2 ^ 59
def prefixEnd_6825249 : Nat := 4983230072969 + 3 ^ 40 * 6825249 * 2
def baseEnd_6825249 : Nat := 3504633323618871915598757

theorem tailTrace_6825249 : CollatzResearch.WordTrace tailWord_6825249 prefixEnd_6825249 3504633323618871915598757 := by
  unfold tailWord_6825249
  simp only [CollatzResearch.WordTrace]
  refine ⟨248937282050296007571398801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165958188033530671714265867 248937282050296007571398801)
  ·
    refine ⟨186702961537722005678549101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248937282050296007571398801 186702961537722005678549101)
    ·
      refine ⟨70013610576645752129455913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186702961537722005678549101 70013610576645752129455913)
      ·
        refine ⟨52510207932484314097091935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70013610576645752129455913 52510207932484314097091935)
        ·
          refine ⟨78765311898726471145637903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52510207932484314097091935 78765311898726471145637903)
          ·
            refine ⟨118147967848089706718456855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78765311898726471145637903 118147967848089706718456855)
            ·
              refine ⟨177221951772134560077685283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118147967848089706718456855 177221951772134560077685283)
              ·
                refine ⟨265832927658201840116527925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177221951772134560077685283 265832927658201840116527925)
                ·
                  refine ⟨24921836967956422510924493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 265832927658201840116527925 24921836967956422510924493)
                  ·
                    refine ⟨9345688862983658441596685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24921836967956422510924493 9345688862983658441596685)
                    ·
                      refine ⟨3504633323618871915598757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9345688862983658441596685 3504633323618871915598757)
                      ·
                        rfl

theorem cell23_6825249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_6825249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825249 prefixEnd_6825249 := by exact prefixLift 6825249
  have htrace : WordTrace (prefixWord ++ tailWord_6825249) baseStart_6825249 baseEnd_6825249 := by
    simpa [prefixWord, tailWord_6825249, baseEnd_6825249] using wordTrace_append hprefix tailTrace_6825249
  have hstable : (prefixWord ++ tailWord_6825249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825249).length < 2 ^ (prefixWord ++ tailWord_6825249).sum := by decide
  have hdescent : baseEnd_6825249 < baseStart_6825249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825256 : List Nat := [2, 1, 5, 1, 2, 3, 1, 8]
def baseStart_6825256 : Nat := 118140960795 + 6825256 * 2 ^ 59
def prefixEnd_6825256 : Nat := 4983230072969 + 3 ^ 40 * 6825256 * 2
def baseEnd_6825256 : Nat := 129801367332720495859675

theorem tailTrace_6825256 : CollatzResearch.WordTrace tailWord_6825256 prefixEnd_6825256 129801367332720495859675 := by
  unfold tailWord_6825256
  simp only [CollatzResearch.WordTrace]
  refine ⟨124468768680635323883451811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165958358240847098511269081 124468768680635323883451811)
  ·
    refine ⟨186703153020952985825177717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124468768680635323883451811 186703153020952985825177717)
    ·
      refine ⟨17503420595714342421110411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 186703153020952985825177717 17503420595714342421110411)
      ·
        refine ⟨26255130893571513631665617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17503420595714342421110411 26255130893571513631665617)
        ·
          refine ⟨19691348170178635223749213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26255130893571513631665617 19691348170178635223749213)
          ·
            refine ⟨7384255563816988208905955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19691348170178635223749213 7384255563816988208905955)
            ·
              refine ⟨11076383345725482313358933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7384255563816988208905955 11076383345725482313358933)
              ·
                refine ⟨129801367332720495859675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11076383345725482313358933 129801367332720495859675)
                ·
                  rfl

theorem cell23_6825256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 8].length) (baseStart_6825256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825256 prefixEnd_6825256 := by exact prefixLift 6825256
  have htrace : WordTrace (prefixWord ++ tailWord_6825256) baseStart_6825256 baseEnd_6825256 := by
    simpa [prefixWord, tailWord_6825256, baseEnd_6825256] using wordTrace_append hprefix tailTrace_6825256
  have hstable : (prefixWord ++ tailWord_6825256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825256).length < 2 ^ (prefixWord ++ tailWord_6825256).sum := by decide
  have hdescent : baseEnd_6825256 < baseStart_6825256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825266 : List Nat := [3, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3]
def baseStart_6825266 : Nat := 118140960795 + 6825266 * 2 ^ 59
def prefixEnd_6825266 : Nat := 4983230072969 + 3 ^ 40 * 6825266 * 2
def baseEnd_6825266 : Nat := 3504642052789998349086179

theorem tailTrace_6825266 : CollatzResearch.WordTrace tailWord_6825266 prefixEnd_6825266 3504642052789998349086179 := by
  unfold tailWord_6825266
  simp only [CollatzResearch.WordTrace]
  refine ⟨62234475522808604868691913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165958601394156279649845101 62234475522808604868691913)
  ·
    refine ⟨46675856642106453651518935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62234475522808604868691913 46675856642106453651518935)
    ·
      refine ⟨70013784963159680477278403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46675856642106453651518935 70013784963159680477278403)
      ·
        refine ⟨105020677444739520715917605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70013784963159680477278403 105020677444739520715917605)
        ·
          refine ⟨19691377020888660134234551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105020677444739520715917605 19691377020888660134234551)
          ·
            refine ⟨29537065531332990201351827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19691377020888660134234551 29537065531332990201351827)
            ·
              refine ⟨44305598296999485302027741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29537065531332990201351827 44305598296999485302027741)
              ·
                refine ⟨16614599361374806988260403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44305598296999485302027741 16614599361374806988260403)
                ·
                  refine ⟨24921899042062210482390605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16614599361374806988260403 24921899042062210482390605)
                  ·
                    refine ⟨9345712140773328930896477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24921899042062210482390605 9345712140773328930896477)
                    ·
                      refine ⟨3504642052789998349086179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9345712140773328930896477 3504642052789998349086179)
                      ·
                        rfl

theorem cell23_6825266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_6825266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825266 prefixEnd_6825266 := by exact prefixLift 6825266
  have htrace : WordTrace (prefixWord ++ tailWord_6825266) baseStart_6825266 baseEnd_6825266 := by
    simpa [prefixWord, tailWord_6825266, baseEnd_6825266] using wordTrace_append hprefix tailTrace_6825266
  have hstable : (prefixWord ++ tailWord_6825266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825266).length < 2 ^ (prefixWord ++ tailWord_6825266).sum := by decide
  have hdescent : baseEnd_6825266 < baseStart_6825266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825284 : List Nat := [2, 3, 4, 1, 1, 2, 2, 3, 1, 2, 2]
def baseStart_6825284 : Nat := 118140960795 + 6825284 * 2 ^ 59
def prefixEnd_6825284 : Nat := 4983230072969 + 3 ^ 40 * 6825284 * 2
def baseEnd_6825284 : Nat := 3504651295441779278661097

theorem tailTrace_6825284 : CollatzResearch.WordTrace tailWord_6825284 prefixEnd_6825284 3504651295441779278661097 := by
  unfold tailWord_6825284
  simp only [CollatzResearch.WordTrace]
  refine ⟨124469279302584604274461453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165959039070112805699281937 124469279302584604274461453)
  ·
    refine ⟨46675979738469226602923045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124469279302584604274461453 46675979738469226602923045)
    ·
      refine ⟨8751746200962979988048071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46675979738469226602923045 8751746200962979988048071)
      ·
        refine ⟨13127619301444469982072107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8751746200962979988048071 13127619301444469982072107)
        ·
          refine ⟨19691428952166704973108161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13127619301444469982072107 19691428952166704973108161)
          ·
            refine ⟨14768571714125028729831121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19691428952166704973108161 14768571714125028729831121)
            ·
              refine ⟨11076428785593771547373341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14768571714125028729831121 11076428785593771547373341)
              ·
                refine ⟨4153660794597664330265003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11076428785593771547373341 4153660794597664330265003)
                ·
                  refine ⟨6230491191896496495397505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4153660794597664330265003 6230491191896496495397505)
                  ·
                    refine ⟨4672868393922372371548129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6230491191896496495397505 4672868393922372371548129)
                    ·
                      refine ⟨3504651295441779278661097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4672868393922372371548129 3504651295441779278661097)
                      ·
                        rfl

theorem cell23_6825284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_6825284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825284 prefixEnd_6825284 := by exact prefixLift 6825284
  have htrace : WordTrace (prefixWord ++ tailWord_6825284) baseStart_6825284 baseEnd_6825284 := by
    simpa [prefixWord, tailWord_6825284, baseEnd_6825284] using wordTrace_append hprefix tailTrace_6825284
  have hstable : (prefixWord ++ tailWord_6825284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825284).length < 2 ^ (prefixWord ++ tailWord_6825284).sum := by decide
  have hdescent : baseEnd_6825284 < baseStart_6825284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825306 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 3, 4, 2]
def baseStart_6825306 : Nat := 118140960795 + 6825306 * 2 ^ 59
def prefixEnd_6825306 : Nat := 4983230072969 + 3 ^ 40 * 6825306 * 2
def baseEnd_6825306 : Nat := 3504662592016178192585995

theorem tailTrace_6825306 : CollatzResearch.WordTrace tailWord_6825306 prefixEnd_6825306 3504662592016178192585995 := by
  unfold tailWord_6825306
  simp only [CollatzResearch.WordTrace]
  refine ⟨62234840252772376576555943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165959574007393004204149181 62234840252772376576555943)
  ·
    refine ⟨93352260379158564864833915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62234840252772376576555943 93352260379158564864833915)
    ·
      refine ⟨140028390568737847297250873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93352260379158564864833915 140028390568737847297250873)
      ·
        refine ⟨105021292926553385472938155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140028390568737847297250873 105021292926553385472938155)
        ·
          refine ⟨157531939389830078209407233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105021292926553385472938155 157531939389830078209407233)
          ·
            refine ⟨118148954542372558657055425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157531939389830078209407233 118148954542372558657055425)
            ·
              refine ⟨88611715906779418992791569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118148954542372558657055425 88611715906779418992791569)
              ·
                refine ⟨66458786930084564244593677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88611715906779418992791569 66458786930084564244593677)
                ·
                  refine ⟨24922045098781711591722629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66458786930084564244593677 24922045098781711591722629)
                  ·
                    refine ⟨4672883456021570923447993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24922045098781711591722629 4672883456021570923447993)
                    ·
                      refine ⟨3504662592016178192585995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4672883456021570923447993 3504662592016178192585995)
                      ·
                        rfl

theorem cell23_6825306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 3, 4, 2].length) (baseStart_6825306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825306 prefixEnd_6825306 := by exact prefixLift 6825306
  have htrace : WordTrace (prefixWord ++ tailWord_6825306) baseStart_6825306 baseEnd_6825306 := by
    simpa [prefixWord, tailWord_6825306, baseEnd_6825306] using wordTrace_append hprefix tailTrace_6825306
  have hstable : (prefixWord ++ tailWord_6825306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825306).length < 2 ^ (prefixWord ++ tailWord_6825306).sum := by decide
  have hdescent : baseEnd_6825306 < baseStart_6825306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825329 : List Nat := [1, 2, 2, 2, 1, 2, 4, 2, 7]
def baseStart_6825329 : Nat := 118140960795 + 6825329 * 2 ^ 59
def prefixEnd_6825329 : Nat := 4983230072969 + 3 ^ 40 * 6825329 * 2
def baseEnd_6825329 : Nat := 389408266896803511399821

theorem tailTrace_6825329 : CollatzResearch.WordTrace tailWord_6825329 prefixEnd_6825329 389408266896803511399821 := by
  unfold tailWord_6825329
  simp only [CollatzResearch.WordTrace]
  refine ⟨248940199890006181234311041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165960133260004120822874027 248940199890006181234311041)
  ·
    refine ⟨186705149917504635925733281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248940199890006181234311041 186705149917504635925733281)
    ·
      refine ⟨140028862438128476944299961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186705149917504635925733281 140028862438128476944299961)
      ·
        refine ⟨105021646828596357708224971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140028862438128476944299961 105021646828596357708224971)
        ·
          refine ⟨157532470242894536562337457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105021646828596357708224971 157532470242894536562337457)
          ·
            refine ⟨118149352682170902421753093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157532470242894536562337457 118149352682170902421753093)
            ·
              refine ⟨22153003627907044204078705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118149352682170902421753093 22153003627907044204078705)
              ·
                refine ⟨16614752720930283153059029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22153003627907044204078705 16614752720930283153059029)
                ·
                  refine ⟨389408266896803511399821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16614752720930283153059029 389408266896803511399821)
                  ·
                    rfl

theorem cell23_6825329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 7].length) (baseStart_6825329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825329 prefixEnd_6825329 := by exact prefixLift 6825329
  have htrace : WordTrace (prefixWord ++ tailWord_6825329) baseStart_6825329 baseEnd_6825329 := by
    simpa [prefixWord, tailWord_6825329, baseEnd_6825329] using wordTrace_append hprefix tailTrace_6825329
  have hstable : (prefixWord ++ tailWord_6825329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825329).length < 2 ^ (prefixWord ++ tailWord_6825329).sum := by decide
  have hdescent : baseEnd_6825329 < baseStart_6825329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825369 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 1, 1, 7]
def baseStart_6825369 : Nat := 118140960795 + 6825369 * 2 ^ 59
def prefixEnd_6825369 : Nat := 4983230072969 + 3 ^ 40 * 6825369 * 2
def baseEnd_6825369 : Nat := 3504694941297411446098205

theorem tailTrace_6825369 : CollatzResearch.WordTrace tailWord_6825369 prefixEnd_6825369 3504694941297411446098205 := by
  unfold tailWord_6825369
  simp only [CollatzResearch.WordTrace]
  refine ⟨248941658809861268065767161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165961105873240845377178107 248941658809861268065767161)
  ·
    refine ⟨186706244107395951049325371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248941658809861268065767161 186706244107395951049325371)
    ·
      refine ⟨280059366161093926573988057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186706244107395951049325371 280059366161093926573988057)
      ·
        refine ⟨210044524620820444930491043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280059366161093926573988057 210044524620820444930491043)
        ·
          refine ⟨315066786931230667395736565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210044524620820444930491043 315066786931230667395736565)
          ·
            refine ⟨29537511274802875068350303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 315066786931230667395736565 29537511274802875068350303)
            ·
              refine ⟨44306266912204312602525455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29537511274802875068350303 44306266912204312602525455)
              ·
                refine ⟨66459400368306468903788183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44306266912204312602525455 66459400368306468903788183)
                ·
                  refine ⟨99689100552459703355682275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66459400368306468903788183 99689100552459703355682275)
                  ·
                    refine ⟨149533650828689555033523413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99689100552459703355682275 149533650828689555033523413)
                    ·
                      refine ⟨3504694941297411446098205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149533650828689555033523413 3504694941297411446098205)
                      ·
                        rfl

theorem cell23_6825369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_6825369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825369 prefixEnd_6825369 := by exact prefixLift 6825369
  have htrace : WordTrace (prefixWord ++ tailWord_6825369) baseStart_6825369 baseEnd_6825369 := by
    simpa [prefixWord, tailWord_6825369, baseEnd_6825369] using wordTrace_append hprefix tailTrace_6825369
  have hstable : (prefixWord ++ tailWord_6825369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825369).length < 2 ^ (prefixWord ++ tailWord_6825369).sum := by decide
  have hdescent : baseEnd_6825369 < baseStart_6825369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825374 : List Nat := [4, 3, 1, 2, 2, 1, 1, 3, 2, 2, 2]
def baseStart_6825374 : Nat := 118140960795 + 6825374 * 2 ^ 59
def prefixEnd_6825374 : Nat := 4983230072969 + 3 ^ 40 * 6825374 * 2
def baseEnd_6825374 : Nat := 3504697508700683926535683

theorem tailTrace_6825374 : CollatzResearch.WordTrace tailWord_6825374 prefixEnd_6825374 3504697508700683926535683 := by
  unfold tailWord_6825374
  simp only [CollatzResearch.WordTrace]
  refine ⟨31117730146855394239962397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165961227449895435946466117 31117730146855394239962397)
  ·
    refine ⟨11669148805070772839985899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31117730146855394239962397 11669148805070772839985899)
    ·
      refine ⟨17503723207606159259978849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11669148805070772839985899 17503723207606159259978849)
      ·
        refine ⟨13127792405704619444984137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17503723207606159259978849 13127792405704619444984137)
        ·
          refine ⟨9845844304278464583738103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13127792405704619444984137 9845844304278464583738103)
          ·
            refine ⟨14768766456417696875607155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9845844304278464583738103 14768766456417696875607155)
            ·
              refine ⟨22153149684626545313410733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14768766456417696875607155 22153149684626545313410733)
              ·
                refine ⟨8307431131734954492529025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22153149684626545313410733 8307431131734954492529025)
                ·
                  refine ⟨6230573348801215869396769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8307431131734954492529025 6230573348801215869396769)
                  ·
                    refine ⟨4672930011600911902047577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6230573348801215869396769 4672930011600911902047577)
                    ·
                      refine ⟨3504697508700683926535683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4672930011600911902047577 3504697508700683926535683)
                      ·
                        rfl

theorem cell23_6825374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_6825374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825374 prefixEnd_6825374 := by exact prefixLift 6825374
  have htrace : WordTrace (prefixWord ++ tailWord_6825374) baseStart_6825374 baseEnd_6825374 := by
    simpa [prefixWord, tailWord_6825374, baseEnd_6825374] using wordTrace_append hprefix tailTrace_6825374
  have hstable : (prefixWord ++ tailWord_6825374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825374).length < 2 ^ (prefixWord ++ tailWord_6825374).sum := by decide
  have hdescent : baseEnd_6825374 < baseStart_6825374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825419 : List Nat := [1, 1, 1, 1, 3, 3, 2, 3, 8]
def baseStart_6825419 : Nat := 118140960795 + 6825419 * 2 ^ 59
def prefixEnd_6825419 : Nat := 4983230072969 + 3 ^ 40 * 6825419 * 2
def baseEnd_6825419 : Nat := 389413401703348472274775

theorem tailTrace_6825419 : CollatzResearch.WordTrace tailWord_6825419 prefixEnd_6825419 389413401703348472274775 := by
  unfold tailWord_6825419
  simp only [CollatzResearch.WordTrace]
  refine ⟨248943482459680126605087311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165962321639786751070058207 248943482459680126605087311)
  ·
    refine ⟨373415223689520189907630967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248943482459680126605087311 373415223689520189907630967)
    ·
      refine ⟨560122835534280284861446451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373415223689520189907630967 560122835534280284861446451)
      ·
        refine ⟨840184253301420427292169677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560122835534280284861446451 840184253301420427292169677)
        ·
          refine ⟨315069094988032660234563629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 840184253301420427292169677 315069094988032660234563629)
          ·
            refine ⟨118150910620512247587961361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 315069094988032660234563629 118150910620512247587961361)
            ·
              refine ⟨88613182965384185690971021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118150910620512247587961361 88613182965384185690971021)
              ·
                refine ⟨33229943612019069634114133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88613182965384185690971021 33229943612019069634114133)
                ·
                  refine ⟨389413401703348472274775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33229943612019069634114133 389413401703348472274775)
                  ·
                    rfl

theorem cell23_6825419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 8].length) (baseStart_6825419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825419 prefixEnd_6825419 := by exact prefixLift 6825419
  have htrace : WordTrace (prefixWord ++ tailWord_6825419) baseStart_6825419 baseEnd_6825419 := by
    simpa [prefixWord, tailWord_6825419, baseEnd_6825419] using wordTrace_append hprefix tailTrace_6825419
  have hstable : (prefixWord ++ tailWord_6825419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825419).length < 2 ^ (prefixWord ++ tailWord_6825419).sum := by decide
  have hdescent : baseEnd_6825419 < baseStart_6825419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825430 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2]
def baseStart_6825430 : Nat := 118140960795 + 6825430 * 2 ^ 59
def prefixEnd_6825430 : Nat := 4983230072969 + 3 ^ 40 * 6825430 * 2
def baseEnd_6825430 : Nat := 3504726263617335707435425

theorem tailTrace_6825430 : CollatzResearch.WordTrace tailWord_6825430 prefixEnd_6825430 3504726263617335707435425 := by
  unfold tailWord_6825430
  simp only [CollatzResearch.WordTrace]
  refine ⟨15558992728915017217733609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165962589108426850322491829 15558992728915017217733609)
  ·
    refine ⟨11669244546686262913300207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15558992728915017217733609 11669244546686262913300207)
    ·
      refine ⟨17503866820029394369950311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11669244546686262913300207 17503866820029394369950311)
      ·
        refine ⟨26255800230044091554925467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17503866820029394369950311 26255800230044091554925467)
        ·
          refine ⟨39383700345066137332388201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26255800230044091554925467 39383700345066137332388201)
          ·
            refine ⟨29537775258799602999291151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39383700345066137332388201 29537775258799602999291151)
            ·
              refine ⟨44306662888199404498936727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29537775258799602999291151 44306662888199404498936727)
              ·
                refine ⟨66459994332299106748405091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44306662888199404498936727 66459994332299106748405091)
                ·
                  refine ⟨99689991498448660122607637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66459994332299106748405091 99689991498448660122607637)
                  ·
                    refine ⟨4672968351489780943247233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 99689991498448660122607637 4672968351489780943247233)
                    ·
                      refine ⟨3504726263617335707435425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4672968351489780943247233 3504726263617335707435425)
                      ·
                        rfl

theorem cell23_6825430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_6825430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825430 prefixEnd_6825430 := by exact prefixLift 6825430
  have htrace : WordTrace (prefixWord ++ tailWord_6825430) baseStart_6825430 baseEnd_6825430 := by
    simpa [prefixWord, tailWord_6825430, baseEnd_6825430] using wordTrace_append hprefix tailTrace_6825430
  have hstable : (prefixWord ++ tailWord_6825430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825430).length < 2 ^ (prefixWord ++ tailWord_6825430).sum := by decide
  have hdescent : baseEnd_6825430 < baseStart_6825430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825470 : List Nat := [4, 2, 2, 3, 1, 1, 1, 1, 8]
def baseStart_6825470 : Nat := 118140960795 + 6825470 * 2 ^ 59
def prefixEnd_6825470 : Nat := 4983230072969 + 3 ^ 40 * 6825470 * 2
def baseEnd_6825470 : Nat := 389416311427057283437249

theorem tailTrace_6825470 : CollatzResearch.WordTrace tailWord_6825470 prefixEnd_6825470 389416311427057283437249 := by
  unfold tailWord_6825470
  simp only [CollatzResearch.WordTrace]
  refine ⟨31118167822811920289399233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165963561721663574876795909 31118167822811920289399233)
  ·
    refine ⟨23338625867108940217049425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31118167822811920289399233 23338625867108940217049425)
    ·
      refine ⟨17503969400331705162787069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23338625867108940217049425 17503969400331705162787069)
      ·
        refine ⟨6563988525124389436045151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17503969400331705162787069 6563988525124389436045151)
        ·
          refine ⟨9845982787686584154067727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6563988525124389436045151 9845982787686584154067727)
          ·
            refine ⟨14768974181529876231101591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9845982787686584154067727 14768974181529876231101591)
            ·
              refine ⟨22153461272294814346652387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14768974181529876231101591 22153461272294814346652387)
              ·
                refine ⟨33230191908442221519978581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22153461272294814346652387 33230191908442221519978581)
                ·
                  refine ⟨389416311427057283437249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33230191908442221519978581 389416311427057283437249)
                  ·
                    rfl

theorem cell23_6825470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_6825470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825470 prefixEnd_6825470 := by exact prefixLift 6825470
  have htrace : WordTrace (prefixWord ++ tailWord_6825470) baseStart_6825470 baseEnd_6825470 := by
    simpa [prefixWord, tailWord_6825470, baseEnd_6825470] using wordTrace_append hprefix tailTrace_6825470
  have hstable : (prefixWord ++ tailWord_6825470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825470).length < 2 ^ (prefixWord ++ tailWord_6825470).sum := by decide
  have hdescent : baseEnd_6825470 < baseStart_6825470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825503 : List Nat := [1, 1, 2, 4, 1, 1, 3, 4, 1, 1, 4]
def baseStart_6825503 : Nat := 118140960795 + 6825503 * 2 ^ 59
def prefixEnd_6825503 : Nat := 4983230072969 + 3 ^ 40 * 6825503 * 2
def baseEnd_6825503 : Nat := 3504763747705113921822589

theorem tailTrace_6825503 : CollatzResearch.WordTrace tailWord_6825503 prefixEnd_6825503 3504763747705113921822589 := by
  unfold tailWord_6825503
  simp only [CollatzResearch.WordTrace]
  refine ⟨248946546191375808951145163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165964364127583872634096775 248946546191375808951145163)
  ·
    refine ⟨373419819287063713426717745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248946546191375808951145163 373419819287063713426717745)
    ·
      refine ⟨280064864465297785070038309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373419819287063713426717745 280064864465297785070038309)
      ·
        refine ⟨52512162087243334700632183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 280064864465297785070038309 52512162087243334700632183)
        ·
          refine ⟨78768243130865002050948275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52512162087243334700632183 78768243130865002050948275)
          ·
            refine ⟨118152364696297503076422413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78768243130865002050948275 118152364696297503076422413)
            ·
              refine ⟨44307136761111563653658405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118152364696297503076422413 44307136761111563653658405)
              ·
                refine ⟨8307588142708418185060951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44307136761111563653658405 8307588142708418185060951)
                ·
                  refine ⟨12461382214062627277591427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8307588142708418185060951 12461382214062627277591427)
                  ·
                    refine ⟨18692073321093940916387141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12461382214062627277591427 18692073321093940916387141)
                    ·
                      refine ⟨3504763747705113921822589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18692073321093940916387141 3504763747705113921822589)
                      ·
                        rfl

theorem cell23_6825503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_6825503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825503 prefixEnd_6825503 := by exact prefixLift 6825503
  have htrace : WordTrace (prefixWord ++ tailWord_6825503) baseStart_6825503 baseEnd_6825503 := by
    simpa [prefixWord, tailWord_6825503, baseEnd_6825503] using wordTrace_append hprefix tailTrace_6825503
  have hstable : (prefixWord ++ tailWord_6825503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825503).length < 2 ^ (prefixWord ++ tailWord_6825503).sum := by decide
  have hdescent : baseEnd_6825503 < baseStart_6825503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825523 : List Nat := [1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 5]
def baseStart_6825523 : Nat := 118140960795 + 6825523 * 2 ^ 59
def prefixEnd_6825523 : Nat := 4983230072969 + 3 ^ 40 * 6825523 * 2
def baseEnd_6825523 : Nat := 3504774017318203843572497

theorem tailTrace_6825523 : CollatzResearch.WordTrace tailWord_6825523 prefixEnd_6825523 3504774017318203843572497 := by
  unfold tailWord_6825523
  simp only [CollatzResearch.WordTrace]
  refine ⟨248947275651303352366873223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165964850434202234911248815 248947275651303352366873223)
  ·
    refine ⟨373420913476955028550309835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248947275651303352366873223 373420913476955028550309835)
    ·
      refine ⟨560131370215432542825464753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373420913476955028550309835 560131370215432542825464753)
      ·
        refine ⟨420098527661574407119098565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 560131370215432542825464753 420098527661574407119098565)
        ·
          refine ⟨78768473936545201334830981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 420098527661574407119098565 78768473936545201334830981)
          ·
            refine ⟨14769088863102225250280809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78768473936545201334830981 14769088863102225250280809)
            ·
              refine ⟨11076816647326668937710607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14769088863102225250280809 11076816647326668937710607)
              ·
                refine ⟨16615224970990003406565911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11076816647326668937710607 16615224970990003406565911)
                ·
                  refine ⟨24922837456485005109848867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16615224970990003406565911 24922837456485005109848867)
                  ·
                    refine ⟨37384256184727507664773301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24922837456485005109848867 37384256184727507664773301)
                    ·
                      refine ⟨3504774017318203843572497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37384256184727507664773301 3504774017318203843572497)
                      ·
                        rfl

theorem cell23_6825523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 5].length) (baseStart_6825523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825523 prefixEnd_6825523 := by exact prefixLift 6825523
  have htrace : WordTrace (prefixWord ++ tailWord_6825523) baseStart_6825523 baseEnd_6825523 := by
    simpa [prefixWord, tailWord_6825523, baseEnd_6825523] using wordTrace_append hprefix tailTrace_6825523
  have hstable : (prefixWord ++ tailWord_6825523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825523).length < 2 ^ (prefixWord ++ tailWord_6825523).sum := by decide
  have hdescent : baseEnd_6825523 < baseStart_6825523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825543 : List Nat := [1, 1, 4, 1, 5, 1, 2, 8]
def baseStart_6825543 : Nat := 118140960795 + 6825543 * 2 ^ 59
def prefixEnd_6825543 : Nat := 4983230072969 + 3 ^ 40 * 6825543 * 2
def baseEnd_6825543 : Nat := 129806825441899769086015

theorem tailTrace_6825543 : CollatzResearch.WordTrace tailWord_6825543 prefixEnd_6825543 129806825441899769086015 := by
  unfold tailWord_6825543
  simp only [CollatzResearch.WordTrace]
  refine ⟨248948005111230895782601283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165965336740820597188400855 248948005111230895782601283)
  ·
    refine ⟨373422007666846343673901925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248948005111230895782601283 373422007666846343673901925)
    ·
      refine ⟨70016626437533689438856611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 373422007666846343673901925 70016626437533689438856611)
      ·
        refine ⟨105024939656300534158284917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70016626437533689438856611 105024939656300534158284917)
        ·
          refine ⟨9846088092778175077339211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105024939656300534158284917 9846088092778175077339211)
          ·
            refine ⟨14769132139167262616008817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9846088092778175077339211 14769132139167262616008817)
            ·
              refine ⟨11076849104375446962006613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14769132139167262616008817 11076849104375446962006613)
              ·
                refine ⟨129806825441899769086015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11076849104375446962006613 129806825441899769086015)
                ·
                  rfl

theorem cell23_6825543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 8].length) (baseStart_6825543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825543 prefixEnd_6825543 := by exact prefixLift 6825543
  have htrace : WordTrace (prefixWord ++ tailWord_6825543) baseStart_6825543 baseEnd_6825543 := by
    simpa [prefixWord, tailWord_6825543, baseEnd_6825543] using wordTrace_append hprefix tailTrace_6825543
  have hstable : (prefixWord ++ tailWord_6825543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825543).length < 2 ^ (prefixWord ++ tailWord_6825543).sum := by decide
  have hdescent : baseEnd_6825543 < baseStart_6825543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825546 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 2, 2, 6]
def baseStart_6825546 : Nat := 118140960795 + 6825546 * 2 ^ 59
def prefixEnd_6825546 : Nat := 4983230072969 + 3 ^ 40 * 6825546 * 2
def baseEnd_6825546 : Nat := 3504785827373257253584891

theorem tailTrace_6825546 : CollatzResearch.WordTrace tailWord_6825546 prefixEnd_6825546 3504785827373257253584891 := by
  unfold tailWord_6825546
  simp only [CollatzResearch.WordTrace]
  refine ⟨62237028632555006823740123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165965409686813351529973661 62237028632555006823740123)
  ·
    refine ⟨93355542948832510235610185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62237028632555006823740123 93355542948832510235610185)
    ·
      refine ⟨70016657211624382676707639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93355542948832510235610185 70016657211624382676707639)
      ·
        refine ⟨105024985817436574015061459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70016657211624382676707639 105024985817436574015061459)
        ·
          refine ⟨157537478726154861022592189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105024985817436574015061459 157537478726154861022592189)
          ·
            refine ⟨59076554522308072883472071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157537478726154861022592189 59076554522308072883472071)
            ·
              refine ⟨88614831783462109325208107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59076554522308072883472071 88614831783462109325208107)
              ·
                refine ⟨132922247675193163987812161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88614831783462109325208107 132922247675193163987812161)
                ·
                  refine ⟨99691685756394872990859121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132922247675193163987812161 99691685756394872990859121)
                  ·
                    refine ⟨74768764317296154743144341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99691685756394872990859121 74768764317296154743144341)
                    ·
                      refine ⟨3504785827373257253584891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74768764317296154743144341 3504785827373257253584891)
                      ·
                        rfl

theorem cell23_6825546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_6825546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825546 prefixEnd_6825546 := by exact prefixLift 6825546
  have htrace : WordTrace (prefixWord ++ tailWord_6825546) baseStart_6825546 baseEnd_6825546 := by
    simpa [prefixWord, tailWord_6825546, baseEnd_6825546] using wordTrace_append hprefix tailTrace_6825546
  have hstable : (prefixWord ++ tailWord_6825546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825546).length < 2 ^ (prefixWord ++ tailWord_6825546).sum := by decide
  have hdescent : baseEnd_6825546 < baseStart_6825546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825553 : List Nat := [1, 2, 2, 1, 3, 2, 2, 3, 1, 3, 3]
def baseStart_6825553 : Nat := 118140960795 + 6825553 * 2 ^ 59
def prefixEnd_6825553 : Nat := 4983230072969 + 3 ^ 40 * 6825553 * 2
def baseEnd_6825553 : Nat := 3504789421737838726197359

theorem tailTrace_6825553 : CollatzResearch.WordTrace tailWord_6825553 prefixEnd_6825553 3504789421737838726197359 := by
  unfold tailWord_6825553
  simp only [CollatzResearch.WordTrace]
  refine ⟨248948369841194667490465313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165965579894129778326976875 248948369841194667490465313)
  ·
    refine ⟨186711277380896000617848985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248948369841194667490465313 186711277380896000617848985)
    ·
      refine ⟨140033458035672000463386739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186711277380896000617848985 140033458035672000463386739)
      ·
        refine ⟨210050187053508000695080109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140033458035672000463386739 210050187053508000695080109)
        ·
          refine ⟨78768820145065500260655041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210050187053508000695080109 78768820145065500260655041)
          ·
            refine ⟨59076615108799125195491281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78768820145065500260655041 59076615108799125195491281)
            ·
              refine ⟨44307461331599343896618461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59076615108799125195491281 44307461331599343896618461)
              ·
                refine ⟨16615297999349753961231923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44307461331599343896618461 16615297999349753961231923)
                ·
                  refine ⟨24922946999024630941847885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16615297999349753961231923 24922946999024630941847885)
                  ·
                    refine ⟨9346105124634236603192957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24922946999024630941847885 9346105124634236603192957)
                    ·
                      refine ⟨3504789421737838726197359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9346105124634236603192957 3504789421737838726197359)
                      ·
                        rfl

theorem cell23_6825553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 3, 3].length) (baseStart_6825553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825553 prefixEnd_6825553 := by exact prefixLift 6825553
  have htrace : WordTrace (prefixWord ++ tailWord_6825553) baseStart_6825553 baseEnd_6825553 := by
    simpa [prefixWord, tailWord_6825553, baseEnd_6825553] using wordTrace_append hprefix tailTrace_6825553
  have hstable : (prefixWord ++ tailWord_6825553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825553).length < 2 ^ (prefixWord ++ tailWord_6825553).sum := by decide
  have hdescent : baseEnd_6825553 < baseStart_6825553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825650 : List Nat := [3, 2, 1, 1, 1, 2, 4, 4, 5]
def baseStart_6825650 : Nat := 118140960795 + 6825650 * 2 ^ 59
def prefixEnd_6825650 : Nat := 4983230072969 + 3 ^ 40 * 6825650 * 2
def baseEnd_6825650 : Nat := 389426581040147205187157

theorem tailTrace_6825650 : CollatzResearch.WordTrace tailWord_6825650 prefixEnd_6825650 389426581040147205187157 := by
  unfold tailWord_6825650
  simp only [CollatzResearch.WordTrace]
  refine ⟨62237976930460813264186601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165967938481228835371164269 62237976930460813264186601)
  ·
    refine ⟨46678482697845609948139951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62237976930460813264186601 46678482697845609948139951)
    ·
      refine ⟨70017724046768414922209927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46678482697845609948139951 70017724046768414922209927)
      ·
        refine ⟨105026586070152622383314891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70017724046768414922209927 105026586070152622383314891)
        ·
          refine ⟨157539879105228933574972337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105026586070152622383314891 157539879105228933574972337)
          ·
            refine ⟨118154909328921700181229253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157539879105228933574972337 118154909328921700181229253)
            ·
              refine ⟨22154045499172818783980485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118154909328921700181229253 22154045499172818783980485)
              ·
                refine ⟨4153883531094903521996341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22154045499172818783980485 4153883531094903521996341)
                ·
                  refine ⟨389426581040147205187157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4153883531094903521996341 389426581040147205187157)
                  ·
                    rfl

theorem cell23_6825650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 4, 5].length) (baseStart_6825650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825650 prefixEnd_6825650 := by exact prefixLift 6825650
  have htrace : WordTrace (prefixWord ++ tailWord_6825650) baseStart_6825650 baseEnd_6825650 := by
    simpa [prefixWord, tailWord_6825650, baseEnd_6825650] using wordTrace_append hprefix tailTrace_6825650
  have hstable : (prefixWord ++ tailWord_6825650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825650).length < 2 ^ (prefixWord ++ tailWord_6825650).sum := by decide
  have hdescent : baseEnd_6825650 < baseStart_6825650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825660 : List Nat := [2, 2, 2, 3, 1, 2, 2, 1, 2, 3, 3]
def baseStart_6825660 : Nat := 118140960795 + 6825660 * 2 ^ 59
def prefixEnd_6825660 : Nat := 4983230072969 + 3 ^ 40 * 6825660 * 2
def baseEnd_6825660 : Nat := 3504844364167869807559367

theorem tailTrace_6825660 : CollatzResearch.WordTrace tailWord_6825660 prefixEnd_6825660 3504844364167869807559367 := by
  unfold tailWord_6825660
  simp only [CollatzResearch.WordTrace]
  refine ⟨124476136225903512382305217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165968181634538016509740289 124476136225903512382305217)
  ·
    refine ⟨93357102169427634286728913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124476136225903512382305217 93357102169427634286728913)
    ·
      refine ⟨70017826627070725715046685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93357102169427634286728913 70017826627070725715046685)
      ·
        refine ⟨26256684985151522143142507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70017826627070725715046685 26256684985151522143142507)
        ·
          refine ⟨39385027477727283214713761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26256684985151522143142507 39385027477727283214713761)
          ·
            refine ⟨29538770608295462411035321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39385027477727283214713761 29538770608295462411035321)
            ·
              refine ⟨22154077956221596808276491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29538770608295462411035321 22154077956221596808276491)
              ·
                refine ⟨33231116934332395212414737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22154077956221596808276491 33231116934332395212414737)
                ·
                  refine ⟨24923337700749296409311053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33231116934332395212414737 24923337700749296409311053)
                  ·
                    refine ⟨9346251637780986153491645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24923337700749296409311053 9346251637780986153491645)
                    ·
                      refine ⟨3504844364167869807559367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9346251637780986153491645 3504844364167869807559367)
                      ·
                        rfl

theorem cell23_6825660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_6825660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825660 prefixEnd_6825660 := by exact prefixLift 6825660
  have htrace : WordTrace (prefixWord ++ tailWord_6825660) baseStart_6825660 baseEnd_6825660 := by
    simpa [prefixWord, tailWord_6825660, baseEnd_6825660] using wordTrace_append hprefix tailTrace_6825660
  have hstable : (prefixWord ++ tailWord_6825660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825660).length < 2 ^ (prefixWord ++ tailWord_6825660).sum := by decide
  have hdescent : baseEnd_6825660 < baseStart_6825660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825684 : List Nat := [2, 4, 1, 3, 1, 3, 1, 3, 5]
def baseStart_6825684 : Nat := 118140960795 + 6825684 * 2 ^ 59
def prefixEnd_6825684 : Nat := 4983230072969 + 3 ^ 40 * 6825684 * 2
def baseEnd_6825684 : Nat := 389428520855953079295473

theorem tailTrace_6825684 : CollatzResearch.WordTrace tailWord_6825684 prefixEnd_6825684 389428520855953079295473 := by
  unfold tailWord_6825684
  simp only [CollatzResearch.WordTrace]
  refine ⟨124476573901860038431742053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165968765202480051242322737 124476573901860038431742053)
  ·
    refine ⟨23339357606598757205951635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124476573901860038431742053 23339357606598757205951635)
    ·
      refine ⟨35009036409898135808927453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23339357606598757205951635 35009036409898135808927453)
      ·
        refine ⟨13128388653711800928347795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35009036409898135808927453 13128388653711800928347795)
        ·
          refine ⟨19692582980567701392521693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13128388653711800928347795 19692582980567701392521693)
          ·
            refine ⟨7384718617712888022195635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19692582980567701392521693 7384718617712888022195635)
            ·
              refine ⟨11077077926569332033293453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7384718617712888022195635 11077077926569332033293453)
              ·
                refine ⟨4153904222463499512485045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11077077926569332033293453 4153904222463499512485045)
                ·
                  refine ⟨389428520855953079295473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4153904222463499512485045 389428520855953079295473)
                  ·
                    rfl

theorem cell23_6825684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_6825684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825684 prefixEnd_6825684 := by exact prefixLift 6825684
  have htrace : WordTrace (prefixWord ++ tailWord_6825684) baseStart_6825684 baseEnd_6825684 := by
    simpa [prefixWord, tailWord_6825684, baseEnd_6825684] using wordTrace_append hprefix tailTrace_6825684
  have hstable : (prefixWord ++ tailWord_6825684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825684).length < 2 ^ (prefixWord ++ tailWord_6825684).sum := by decide
  have hdescent : baseEnd_6825684 < baseStart_6825684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825700 : List Nat := [2, 3, 1, 1, 1, 3, 3, 2, 2, 1, 4]
def baseStart_6825700 : Nat := 118140960795 + 6825700 * 2 ^ 59
def prefixEnd_6825700 : Nat := 4983230072969 + 3 ^ 40 * 6825700 * 2
def baseEnd_6825700 : Nat := 3504864903394049651059183

theorem tailTrace_6825700 : CollatzResearch.WordTrace tailWord_6825700 prefixEnd_6825700 3504864903394049651059183 := by
  unfold tailWord_6825700
  simp only [CollatzResearch.WordTrace]
  refine ⟨124476865685831055798033277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165969154247774741064044369 124476865685831055798033277)
  ·
    refine ⟨46678824632186645924262479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124476865685831055798033277 46678824632186645924262479)
    ·
      refine ⟨70018236948279968886393719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46678824632186645924262479 70018236948279968886393719)
      ·
        refine ⟨105027355422419953329590579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70018236948279968886393719 105027355422419953329590579)
        ·
          refine ⟨157541033133629929994385869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105027355422419953329590579 157541033133629929994385869)
          ·
            refine ⟨59077887425111223747894701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157541033133629929994385869 59077887425111223747894701)
            ·
              refine ⟨22154207784416708905460513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59077887425111223747894701 22154207784416708905460513)
              ·
                refine ⟨16615655838312531679095385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22154207784416708905460513 16615655838312531679095385)
                ·
                  refine ⟨12461741878734398759321539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16615655838312531679095385 12461741878734398759321539)
                  ·
                    refine ⟨18692612818101598138982309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12461741878734398759321539 18692612818101598138982309)
                    ·
                      refine ⟨3504864903394049651059183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18692612818101598138982309 3504864903394049651059183)
                      ·
                        rfl

theorem cell23_6825700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_6825700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825700 prefixEnd_6825700 := by exact prefixLift 6825700
  have htrace : WordTrace (prefixWord ++ tailWord_6825700) baseStart_6825700 baseEnd_6825700 := by
    simpa [prefixWord, tailWord_6825700, baseEnd_6825700] using wordTrace_append hprefix tailTrace_6825700
  have hstable : (prefixWord ++ tailWord_6825700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825700).length < 2 ^ (prefixWord ++ tailWord_6825700).sum := by decide
  have hdescent : baseEnd_6825700 < baseStart_6825700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825761 : List Nat := [1, 2, 3, 2, 1, 5, 2, 2, 1, 4]
def baseStart_6825761 : Nat := 118140960795 + 6825761 * 2 ^ 59
def prefixEnd_6825761 : Nat := 4983230072969 + 3 ^ 40 * 6825761 * 2
def baseEnd_6825761 : Nat := 1168298741904657970798801

theorem tailTrace_6825761 : CollatzResearch.WordTrace tailWord_6825761 prefixEnd_6825761 1168298741904657970798801 := by
  unfold tailWord_6825761
  simp only [CollatzResearch.WordTrace]
  refine ⟨248955956224441119014037137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165970637482960746009358091 248955956224441119014037137)
  ·
    refine ⟨186716967168330839260527853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248955956224441119014037137 186716967168330839260527853)
    ·
      refine ⟨70018862688124064722697945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186716967168330839260527853 70018862688124064722697945)
      ·
        refine ⟨52514147016093048542023459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70018862688124064722697945 52514147016093048542023459)
        ·
          refine ⟨78771220524139572813035189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52514147016093048542023459 78771220524139572813035189)
          ·
            refine ⟨7384801924138084951222049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78771220524139572813035189 7384801924138084951222049)
            ·
              refine ⟨5538601443103563713416537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7384801924138084951222049 5538601443103563713416537)
              ·
                refine ⟨4153951082327672785062403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5538601443103563713416537 4153951082327672785062403)
                ·
                  refine ⟨6230926623491509177593605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4153951082327672785062403 6230926623491509177593605)
                  ·
                    refine ⟨1168298741904657970798801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6230926623491509177593605 1168298741904657970798801)
                    ·
                      rfl

theorem cell23_6825761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_6825761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825761 prefixEnd_6825761 := by exact prefixLift 6825761
  have htrace : WordTrace (prefixWord ++ tailWord_6825761) baseStart_6825761 baseEnd_6825761 := by
    simpa [prefixWord, tailWord_6825761, baseEnd_6825761] using wordTrace_append hprefix tailTrace_6825761
  have hstable : (prefixWord ++ tailWord_6825761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825761).length < 2 ^ (prefixWord ++ tailWord_6825761).sum := by decide
  have hdescent : baseEnd_6825761 < baseStart_6825761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825800 : List Nat := [2, 1, 3, 1, 1, 4, 2, 2, 1, 6]
def baseStart_6825800 : Nat := 118140960795 + 6825800 * 2 ^ 59
def prefixEnd_6825800 : Nat := 4983230072969 + 3 ^ 40 * 6825800 * 2
def baseEnd_6825800 : Nat := 1168305417153166419936241

theorem tailTrace_6825800 : CollatzResearch.WordTrace tailWord_6825800 prefixEnd_6825800 1168305417153166419936241 := by
  unfold tailWord_6825800
  simp only [CollatzResearch.WordTrace]
  refine ⟨124478689335649914337353427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165971585780866552449804569 124478689335649914337353427)
  ·
    refine ⟨186718034003474871506030141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124478689335649914337353427 186718034003474871506030141)
    ·
      refine ⟨70019262751303076814761303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186718034003474871506030141 70019262751303076814761303)
      ·
        refine ⟨105028894126954615222141955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70019262751303076814761303 105028894126954615222141955)
        ·
          refine ⟨157543341190431922833212933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105028894126954615222141955 157543341190431922833212933)
          ·
            refine ⟨29539376473205985531227425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157543341190431922833212933 29539376473205985531227425)
            ·
              refine ⟨22154532354904489148420569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29539376473205985531227425 22154532354904489148420569)
              ·
                refine ⟨16615899266178366861315427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22154532354904489148420569 16615899266178366861315427)
                ·
                  refine ⟨24923848899267550291973141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16615899266178366861315427 24923848899267550291973141)
                  ·
                    refine ⟨1168305417153166419936241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24923848899267550291973141 1168305417153166419936241)
                    ·
                      rfl

theorem cell23_6825800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_6825800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825800 prefixEnd_6825800 := by exact prefixLift 6825800
  have htrace : WordTrace (prefixWord ++ tailWord_6825800) baseStart_6825800 baseEnd_6825800 := by
    simpa [prefixWord, tailWord_6825800, baseEnd_6825800] using wordTrace_append hprefix tailTrace_6825800
  have hstable : (prefixWord ++ tailWord_6825800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825800).length < 2 ^ (prefixWord ++ tailWord_6825800).sum := by decide
  have hdescent : baseEnd_6825800 < baseStart_6825800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825824 : List Nat := [2, 1, 1, 3, 3, 2, 1, 3, 3, 2, 2]
def baseStart_6825824 : Nat := 118140960795 + 6825824 * 2 ^ 59
def prefixEnd_6825824 : Nat := 4983230072969 + 3 ^ 40 * 6825824 * 2
def baseEnd_6825824 : Nat := 3504928574995207165908613

theorem tailTrace_6825824 : CollatzResearch.WordTrace tailWord_6825824 prefixEnd_6825824 3504928574995207165908613 := by
  unfold tailWord_6825824
  simp only [CollatzResearch.WordTrace]
  refine ⟨124479127011606440386790263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165972169348808587182387017 124479127011606440386790263)
  ·
    refine ⟨186718690517409660580185395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124479127011606440386790263 186718690517409660580185395)
    ·
      refine ⟨280078035776114490870278093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186718690517409660580185395 280078035776114490870278093)
      ·
        refine ⟨105029263416042934076354285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280078035776114490870278093 105029263416042934076354285)
        ·
          refine ⟨39385973781016100278632857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105029263416042934076354285 39385973781016100278632857)
          ·
            refine ⟨29539480335762075208974643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39385973781016100278632857 29539480335762075208974643)
            ·
              refine ⟨44309220503643112813461965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29539480335762075208974643 44309220503643112813461965)
              ·
                refine ⟨16615957688866167305048237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44309220503643112813461965 16615957688866167305048237)
                ·
                  refine ⟨6230984133324812739393089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16615957688866167305048237 6230984133324812739393089)
                  ·
                    refine ⟨4673238099993609554544817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6230984133324812739393089 4673238099993609554544817)
                    ·
                      refine ⟨3504928574995207165908613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4673238099993609554544817 3504928574995207165908613)
                      ·
                        rfl

theorem cell23_6825824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 3, 2, 2].length) (baseStart_6825824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825824 prefixEnd_6825824 := by exact prefixLift 6825824
  have htrace : WordTrace (prefixWord ++ tailWord_6825824) baseStart_6825824 baseEnd_6825824 := by
    simpa [prefixWord, tailWord_6825824, baseEnd_6825824] using wordTrace_append hprefix tailTrace_6825824
  have hstable : (prefixWord ++ tailWord_6825824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825824).length < 2 ^ (prefixWord ++ tailWord_6825824).sum := by decide
  have hdescent : baseEnd_6825824 < baseStart_6825824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825827 : List Nat := [1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 5]
def baseStart_6825827 : Nat := 118140960795 + 6825827 * 2 ^ 59
def prefixEnd_6825827 : Nat := 4983230072969 + 3 ^ 40 * 6825827 * 2
def baseEnd_6825827 : Nat := 3504930115437170654171099

theorem tailTrace_6825827 : CollatzResearch.WordTrace tailWord_6825827 prefixEnd_6825827 3504930115437170654171099 := by
  unfold tailWord_6825827
  simp only [CollatzResearch.WordTrace]
  refine ⟨248958363442202012285939735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165972242294801341523959823 248958363442202012285939735)
  ·
    refine ⟨373437545163303018428909603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248958363442202012285939735 373437545163303018428909603)
    ·
      refine ⟨560156317744954527643364405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373437545163303018428909603 560156317744954527643364405)
      ·
        refine ⟨52514654788589486966565413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 560156317744954527643364405 52514654788589486966565413)
        ·
          refine ⟨9846497772860528806231015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52514654788589486966565413 9846497772860528806231015)
          ·
            refine ⟨14769746659290793209346523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9846497772860528806231015 14769746659290793209346523)
            ·
              refine ⟨22154619988936189814019785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14769746659290793209346523 22154619988936189814019785)
              ·
                refine ⟨16615964991702142360514839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22154619988936189814019785 16615964991702142360514839)
                ·
                  refine ⟨24923947487553213540772259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16615964991702142360514839 24923947487553213540772259)
                  ·
                    refine ⟨37385921231329820311158389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24923947487553213540772259 37385921231329820311158389)
                    ·
                      refine ⟨3504930115437170654171099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37385921231329820311158389 3504930115437170654171099)
                      ·
                        rfl

theorem cell23_6825827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_6825827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825827 prefixEnd_6825827 := by exact prefixLift 6825827
  have htrace : WordTrace (prefixWord ++ tailWord_6825827) baseStart_6825827 baseEnd_6825827 := by
    simpa [prefixWord, tailWord_6825827, baseEnd_6825827] using wordTrace_append hprefix tailTrace_6825827
  have hstable : (prefixWord ++ tailWord_6825827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825827).length < 2 ^ (prefixWord ++ tailWord_6825827).sum := by decide
  have hdescent : baseEnd_6825827 < baseStart_6825827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825837 : List Nat := [1, 5, 1, 1, 1, 1, 5, 1, 1, 2, 4]
def baseStart_6825837 : Nat := 118140960795 + 6825837 * 2 ^ 59
def prefixEnd_6825837 : Nat := 4983230072969 + 3 ^ 40 * 6825837 * 2
def baseEnd_6825837 : Nat := 3504935250243715615046053

theorem tailTrace_6825837 : CollatzResearch.WordTrace tailWord_6825837 prefixEnd_6825837 3504935250243715615046053 := by
  unfold tailWord_6825837
  simp only [CollatzResearch.WordTrace]
  refine ⟨248958728172165783993803765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165972485448110522662535843 248958728172165783993803765)
  ·
    refine ⟨23339880766140542249419103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 248958728172165783993803765 23339880766140542249419103)
    ·
      refine ⟨35009821149210813374128655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23339880766140542249419103 35009821149210813374128655)
      ·
        refine ⟨52514731723816220061192983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35009821149210813374128655 52514731723816220061192983)
        ·
          refine ⟨78772097585724330091789475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52514731723816220061192983 78772097585724330091789475)
          ·
            refine ⟨118158146378586495137684213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78772097585724330091789475 118158146378586495137684213)
            ·
              refine ⟨11077326222992483919157895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118158146378586495137684213 11077326222992483919157895)
              ·
                refine ⟨16615989334488725878736843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11077326222992483919157895 16615989334488725878736843)
                ·
                  refine ⟨24923984001733088818105265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16615989334488725878736843 24923984001733088818105265)
                  ·
                    refine ⟨18692988001299816613578949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24923984001733088818105265 18692988001299816613578949)
                    ·
                      refine ⟨3504935250243715615046053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18692988001299816613578949 3504935250243715615046053)
                      ·
                        rfl

theorem cell23_6825837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_6825837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825837 prefixEnd_6825837 := by exact prefixLift 6825837
  have htrace : WordTrace (prefixWord ++ tailWord_6825837) baseStart_6825837 baseEnd_6825837 := by
    simpa [prefixWord, tailWord_6825837, baseEnd_6825837] using wordTrace_append hprefix tailTrace_6825837
  have hstable : (prefixWord ++ tailWord_6825837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825837).length < 2 ^ (prefixWord ++ tailWord_6825837).sum := by decide
  have hdescent : baseEnd_6825837 < baseStart_6825837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825867 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 5, 3, 2]
def baseStart_6825867 : Nat := 118140960795 + 6825867 * 2 ^ 59
def prefixEnd_6825867 : Nat := 4983230072969 + 3 ^ 40 * 6825867 * 2
def baseEnd_6825867 : Nat := 3504950654663350497670915

theorem tailTrace_6825867 : CollatzResearch.WordTrace tailWord_6825867 prefixEnd_6825867 3504950654663350497670915 := by
  unfold tailWord_6825867
  simp only [CollatzResearch.WordTrace]
  refine ⟨248959822362057099117395855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165973214908038066078263903 248959822362057099117395855)
  ·
    refine ⟨373439733543085648676093783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248959822362057099117395855 373439733543085648676093783)
    ·
      refine ⟨560159600314628473014140675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373439733543085648676093783 560159600314628473014140675)
      ·
        refine ⟨840239400471942709521211013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560159600314628473014140675 840239400471942709521211013)
        ·
          refine ⟨157544887588489258035227065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 840239400471942709521211013 157544887588489258035227065)
          ·
            refine ⟨118158665691366943526420299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157544887588489258035227065 118158665691366943526420299)
            ·
              refine ⟨177237998537050415289630449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118158665691366943526420299 177237998537050415289630449)
              ·
                refine ⟨132928498902787811467222837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177237998537050415289630449 132928498902787811467222837)
                ·
                  refine ⟨12462046772136357325052141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132928498902787811467222837 12462046772136357325052141)
                  ·
                    refine ⟨4673267539551133996894553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12462046772136357325052141 4673267539551133996894553)
                    ·
                      refine ⟨3504950654663350497670915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4673267539551133996894553 3504950654663350497670915)
                      ·
                        rfl

theorem cell23_6825867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 3, 2].length) (baseStart_6825867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825867 prefixEnd_6825867 := by exact prefixLift 6825867
  have htrace : WordTrace (prefixWord ++ tailWord_6825867) baseStart_6825867 baseEnd_6825867 := by
    simpa [prefixWord, tailWord_6825867, baseEnd_6825867] using wordTrace_append hprefix tailTrace_6825867
  have hstable : (prefixWord ++ tailWord_6825867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825867).length < 2 ^ (prefixWord ++ tailWord_6825867).sum := by decide
  have hdescent : baseEnd_6825867 < baseStart_6825867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825914 : List Nat := [3, 1, 1, 1, 2, 1, 2, 4, 4, 2, 2]
def baseStart_6825914 : Nat := 118140960795 + 6825914 * 2 ^ 59
def prefixEnd_6825914 : Nat := 4983230072969 + 3 ^ 40 * 6825914 * 2
def baseEnd_6825914 : Nat := 3504974788254111813783199

theorem tailTrace_6825914 : CollatzResearch.WordTrace tailWord_6825914 prefixEnd_6825914 3504974788254111813783199 := by
  unfold tailWord_6825914
  simp only [CollatzResearch.WordTrace]
  refine ⟨62240384148221706536089199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165974357728591217429571197 62240384148221706536089199)
  ·
    refine ⟨93360576222332559804133799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62240384148221706536089199 93360576222332559804133799)
    ·
      refine ⟨140040864333498839706200699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93360576222332559804133799 140040864333498839706200699)
      ·
        refine ⟨210061296500248259559301049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140040864333498839706200699 210061296500248259559301049)
        ·
          refine ⟨157545972375186194669475787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210061296500248259559301049 157545972375186194669475787)
          ·
            refine ⟨236318958562779292004213681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157545972375186194669475787 236318958562779292004213681)
            ·
              refine ⟨177239218922084469003160261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236318958562779292004213681 177239218922084469003160261)
              ·
                refine ⟨33232353547890837938092549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177239218922084469003160261 33232353547890837938092549)
                ·
                  refine ⟨6231066290229532113392353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33232353547890837938092549 6231066290229532113392353)
                  ·
                    refine ⟨4673299717672149085044265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6231066290229532113392353 4673299717672149085044265)
                    ·
                      refine ⟨3504974788254111813783199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4673299717672149085044265 3504974788254111813783199)
                      ·
                        rfl

theorem cell23_6825914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 4, 2, 2].length) (baseStart_6825914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825914 prefixEnd_6825914 := by exact prefixLift 6825914
  have htrace : WordTrace (prefixWord ++ tailWord_6825914) baseStart_6825914 baseEnd_6825914 := by
    simpa [prefixWord, tailWord_6825914, baseEnd_6825914] using wordTrace_append hprefix tailTrace_6825914
  have hstable : (prefixWord ++ tailWord_6825914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825914).length < 2 ^ (prefixWord ++ tailWord_6825914).sum := by decide
  have hdescent : baseEnd_6825914 < baseStart_6825914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825917 : List Nat := [1, 4, 1, 2, 3, 1, 2, 1, 2, 1, 5]
def baseStart_6825917 : Nat := 118140960795 + 6825917 * 2 ^ 59
def prefixEnd_6825917 : Nat := 4983230072969 + 3 ^ 40 * 6825917 * 2
def baseEnd_6825917 : Nat := 3504976328696075302045685

theorem tailTrace_6825917 : CollatzResearch.WordTrace tailWord_6825917 prefixEnd_6825917 3504976328696075302045685 := by
  unfold tailWord_6825917
  simp only [CollatzResearch.WordTrace]
  refine ⟨248961646011875957656716005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165974430674583971771144003 248961646011875957656716005)
  ·
    refine ⟨46680308627226742060634251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248961646011875957656716005 46680308627226742060634251)
    ·
      refine ⟨70020462940840113090951377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46680308627226742060634251 70020462940840113090951377)
      ·
        refine ⟨52515347205630084818213533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70020462940840113090951377 52515347205630084818213533)
        ·
          refine ⟨19693255202111281806830075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52515347205630084818213533 19693255202111281806830075)
          ·
            refine ⟨29539882803166922710245113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19693255202111281806830075 29539882803166922710245113)
            ·
              refine ⟨22154912102375192032683835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29539882803166922710245113 22154912102375192032683835)
              ·
                refine ⟨33232368153562788049025753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22154912102375192032683835 33232368153562788049025753)
                ·
                  refine ⟨24924276115172091036769315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33232368153562788049025753 24924276115172091036769315)
                  ·
                    refine ⟨37386414172758136555153973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24924276115172091036769315 37386414172758136555153973)
                    ·
                      refine ⟨3504976328696075302045685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37386414172758136555153973 3504976328696075302045685)
                      ·
                        rfl

theorem cell23_6825917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_6825917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825917 prefixEnd_6825917 := by exact prefixLift 6825917
  have htrace : WordTrace (prefixWord ++ tailWord_6825917) baseStart_6825917 baseEnd_6825917 := by
    simpa [prefixWord, tailWord_6825917, baseEnd_6825917] using wordTrace_append hprefix tailTrace_6825917
  have hstable : (prefixWord ++ tailWord_6825917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825917).length < 2 ^ (prefixWord ++ tailWord_6825917).sum := by decide
  have hdescent : baseEnd_6825917 < baseStart_6825917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825918 : List Nat := [4, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2]
def baseStart_6825918 : Nat := 118140960795 + 6825918 * 2 ^ 59
def prefixEnd_6825918 : Nat := 4983230072969 + 3 ^ 40 * 6825918 * 2
def baseEnd_6825918 : Nat := 3504976842176729798133181

theorem tailTrace_6825918 : CollatzResearch.WordTrace tailWord_6825918 prefixEnd_6825918 3504976842176729798133181 := by
  unfold tailWord_6825918
  simp only [CollatzResearch.WordTrace]
  refine ⟨31120210310609041853437801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165974454989914889885001605 31120210310609041853437801)
  ·
    refine ⟨23340157732956781390078351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31120210310609041853437801 23340157732956781390078351)
    ·
      refine ⟨35010236599435172085117527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23340157732956781390078351 35010236599435172085117527)
      ·
        refine ⟨52515354899152758127676291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35010236599435172085117527 52515354899152758127676291)
        ·
          refine ⟨78773032348729137191514437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52515354899152758127676291 78773032348729137191514437)
          ·
            refine ⟨14769943565386713223408957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78773032348729137191514437 14769943565386713223408957)
            ·
              refine ⟨5538728837020017458778359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14769943565386713223408957 5538728837020017458778359)
              ·
                refine ⟨8308093255530026188167539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5538728837020017458778359 8308093255530026188167539)
                ·
                  refine ⟨12462139883295039282251309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8308093255530026188167539 12462139883295039282251309)
                  ·
                    refine ⟨4673302456235639730844241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12462139883295039282251309 4673302456235639730844241)
                    ·
                      refine ⟨3504976842176729798133181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4673302456235639730844241 3504976842176729798133181)
                      ·
                        rfl

theorem cell23_6825918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_6825918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825918 prefixEnd_6825918 := by exact prefixLift 6825918
  have htrace : WordTrace (prefixWord ++ tailWord_6825918) baseStart_6825918 baseEnd_6825918 := by
    simpa [prefixWord, tailWord_6825918, baseEnd_6825918] using wordTrace_append hprefix tailTrace_6825918
  have hstable : (prefixWord ++ tailWord_6825918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825918).length < 2 ^ (prefixWord ++ tailWord_6825918).sum := by decide
  have hdescent : baseEnd_6825918 < baseStart_6825918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825930 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 1, 2, 7]
def baseStart_6825930 : Nat := 118140960795 + 6825930 * 2 ^ 59
def prefixEnd_6825930 : Nat := 4983230072969 + 3 ^ 40 * 6825930 * 2
def baseEnd_6825930 : Nat := 3504983003944583751183125

theorem tailTrace_6825930 : CollatzResearch.WordTrace tailWord_6825930 prefixEnd_6825930 3504983003944583751183125 := by
  unfold tailWord_6825930
  simp only [CollatzResearch.WordTrace]
  refine ⟨62240530040207215219234811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165974746773885907251292829 62240530040207215219234811)
  ·
    refine ⟨93360795060310822828852217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62240530040207215219234811 93360795060310822828852217)
    ·
      refine ⟨70020596295233117121639163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93360795060310822828852217 70020596295233117121639163)
      ·
        refine ⟨105030894442849675682458745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70020596295233117121639163 105030894442849675682458745)
        ·
          refine ⟨78773170832137256761844059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105030894442849675682458745 78773170832137256761844059)
          ·
            refine ⟨118159756248205885142766089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78773170832137256761844059 118159756248205885142766089)
            ·
              refine ⟨88619817186154413857074567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118159756248205885142766089 88619817186154413857074567)
              ·
                refine ⟨132929725779231620785611851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88619817186154413857074567 132929725779231620785611851)
                ·
                  refine ⟨199394588668847431178417777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132929725779231620785611851 199394588668847431178417777)
                  ·
                    refine ⟨149545941501635573383813333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 199394588668847431178417777 149545941501635573383813333)
                    ·
                      refine ⟨3504983003944583751183125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149545941501635573383813333 3504983003944583751183125)
                      ·
                        rfl

theorem cell23_6825930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_6825930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825930 prefixEnd_6825930 := by exact prefixLift 6825930
  have htrace : WordTrace (prefixWord ++ tailWord_6825930) baseStart_6825930 baseEnd_6825930 := by
    simpa [prefixWord, tailWord_6825930, baseEnd_6825930] using wordTrace_append hprefix tailTrace_6825930
  have hstable : (prefixWord ++ tailWord_6825930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825930).length < 2 ^ (prefixWord ++ tailWord_6825930).sum := by decide
  have hdescent : baseEnd_6825930 < baseStart_6825930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825931 : List Nat := [1, 1, 1, 1, 3, 4, 4, 2, 2, 2, 2]
def baseStart_6825931 : Nat := 118140960795 + 6825931 * 2 ^ 59
def prefixEnd_6825931 : Nat := 4983230072969 + 3 ^ 40 * 6825931 * 2
def baseEnd_6825931 : Nat := 3504983517425238247270621

theorem tailTrace_6825931 : CollatzResearch.WordTrace tailWord_6825931 prefixEnd_6825931 3504983517425238247270621 := by
  unfold tailWord_6825931
  simp only [CollatzResearch.WordTrace]
  refine ⟨248962156633825238047725647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165974771089216825365150431 248962156633825238047725647)
  ·
    refine ⟨373443234950737857071588471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248962156633825238047725647 373443234950737857071588471)
    ·
      refine ⟨560164852426106785607382707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373443234950737857071588471 560164852426106785607382707)
      ·
        refine ⟨840247278639160178411074061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560164852426106785607382707 840247278639160178411074061)
        ·
          refine ⟨315092729489685066904152773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 840247278639160178411074061 315092729489685066904152773)
          ·
            refine ⟨59079886779315950044528645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 315092729489685066904152773 59079886779315950044528645)
            ·
              refine ⟨11077478771121740633349121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59079886779315950044528645 11077478771121740633349121)
              ·
                refine ⟨8308109078341305475011841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11077478771121740633349121 8308109078341305475011841)
                ·
                  refine ⟨6231081808755979106258881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8308109078341305475011841 6231081808755979106258881)
                  ·
                    refine ⟨4673311356566984329694161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6231081808755979106258881 4673311356566984329694161)
                    ·
                      refine ⟨3504983517425238247270621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4673311356566984329694161 3504983517425238247270621)
                      ·
                        rfl

theorem cell23_6825931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 2, 2, 2].length) (baseStart_6825931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825931 prefixEnd_6825931 := by exact prefixLift 6825931
  have htrace : WordTrace (prefixWord ++ tailWord_6825931) baseStart_6825931 baseEnd_6825931 := by
    simpa [prefixWord, tailWord_6825931, baseEnd_6825931] using wordTrace_append hprefix tailTrace_6825931
  have hstable : (prefixWord ++ tailWord_6825931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825931).length < 2 ^ (prefixWord ++ tailWord_6825931).sum := by decide
  have hdescent : baseEnd_6825931 < baseStart_6825931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6825987 : List Nat := [1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 4]
def baseStart_6825987 : Nat := 118140960795 + 6825987 * 2 ^ 59
def prefixEnd_6825987 : Nat := 4983230072969 + 3 ^ 40 * 6825987 * 2
def baseEnd_6825987 : Nat := 3505012272341890028170363

theorem tailTrace_6825987 : CollatzResearch.WordTrace tailWord_6825987 prefixEnd_6825987 3505012272341890028170363 := by
  unfold tailWord_6825987
  simp only [CollatzResearch.WordTrace]
  refine ⟨248964199121622359611764215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165976132747748239741176143 248964199121622359611764215)
  ·
    refine ⟨373446298682433539417646323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248964199121622359611764215 373446298682433539417646323)
    ·
      refine ⟨560169448023650309126469485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373446298682433539417646323 560169448023650309126469485)
      ·
        refine ⟨210063543008868865922426057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 560169448023650309126469485 210063543008868865922426057)
        ·
          refine ⟨157547657256651649441819543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210063543008868865922426057 157547657256651649441819543)
          ·
            refine ⟨236321485884977474162729315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157547657256651649441819543 236321485884977474162729315)
            ·
              refine ⟨354482228827466211244093973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236321485884977474162729315 354482228827466211244093973)
              ·
                refine ⟨16616354476287478652066905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 354482228827466211244093973 16616354476287478652066905)
                ·
                  refine ⟨12462265857215608989050179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16616354476287478652066905 12462265857215608989050179)
                  ·
                    refine ⟨18693398785823413483575269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12462265857215608989050179 18693398785823413483575269)
                    ·
                      refine ⟨3505012272341890028170363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18693398785823413483575269 3505012272341890028170363)
                      ·
                        rfl

theorem cell23_6825987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_6825987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6825987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6825987 prefixEnd_6825987 := by exact prefixLift 6825987
  have htrace : WordTrace (prefixWord ++ tailWord_6825987) baseStart_6825987 baseEnd_6825987 := by
    simpa [prefixWord, tailWord_6825987, baseEnd_6825987] using wordTrace_append hprefix tailTrace_6825987
  have hstable : (prefixWord ++ tailWord_6825987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6825987).length < 2 ^ (prefixWord ++ tailWord_6825987).sum := by decide
  have hdescent : baseEnd_6825987 < baseStart_6825987 := by decide
  rcases family_descends (prefixWord ++ tailWord_6825987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826041 : List Nat := [1, 2, 1, 5, 3, 1, 1, 2, 2, 2, 3]
def baseStart_6826041 : Nat := 118140960795 + 6826041 * 2 ^ 59
def prefixEnd_6826041 : Nat := 4983230072969 + 3 ^ 40 * 6826041 * 2
def baseEnd_6826041 : Nat := 3505040000297232816895115

theorem tailTrace_6826041 : CollatzResearch.WordTrace tailWord_6826041 prefixEnd_6826041 3505040000297232816895115 := by
  unfold tailWord_6826041
  simp only [CollatzResearch.WordTrace]
  refine ⟨248966168663426726834229977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165977445775617817889486651 248966168663426726834229977)
  ·
    refine ⟨186724626497570045125672483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248966168663426726834229977 186724626497570045125672483)
    ·
      refine ⟨280086939746355067688508725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186724626497570045125672483 280086939746355067688508725)
      ·
        refine ⟨26258150601220787595797693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 280086939746355067688508725 26258150601220787595797693)
        ·
          refine ⟨9846806475457795348424135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26258150601220787595797693 9846806475457795348424135)
          ·
            refine ⟨14770209713186693022636203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9846806475457795348424135 14770209713186693022636203)
            ·
              refine ⟨22155314569780039533954305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14770209713186693022636203 22155314569780039533954305)
              ·
                refine ⟨16616485927335029650465729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22155314569780039533954305 16616485927335029650465729)
                ·
                  refine ⟨12462364445501272237849297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16616485927335029650465729 12462364445501272237849297)
                  ·
                    refine ⟨9346773334125954178386973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12462364445501272237849297 9346773334125954178386973)
                    ·
                      refine ⟨3505040000297232816895115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9346773334125954178386973 3505040000297232816895115)
                      ·
                        rfl

theorem cell23_6826041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_6826041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826041 prefixEnd_6826041 := by exact prefixLift 6826041
  have htrace : WordTrace (prefixWord ++ tailWord_6826041) baseStart_6826041 baseEnd_6826041 := by
    simpa [prefixWord, tailWord_6826041, baseEnd_6826041] using wordTrace_append hprefix tailTrace_6826041
  have hstable : (prefixWord ++ tailWord_6826041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826041).length < 2 ^ (prefixWord ++ tailWord_6826041).sum := by decide
  have hdescent : baseEnd_6826041 < baseStart_6826041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826048 : List Nat := [2, 1, 1, 2, 2, 5, 3, 2, 1, 4]
def baseStart_6826048 : Nat := 118140960795 + 6826048 * 2 ^ 59
def prefixEnd_6826048 : Nat := 4983230072969 + 3 ^ 40 * 6826048 * 2
def baseEnd_6826048 : Nat := 1168347864887271429835861

theorem tailTrace_6826048 : CollatzResearch.WordTrace tailWord_6826048 prefixEnd_6826048 1168347864887271429835861 := by
  unfold tailWord_6826048
  simp only [CollatzResearch.WordTrace]
  refine ⟨124483211987200683514867399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165977615982934244686489865 124483211987200683514867399)
  ·
    refine ⟨186724817980801025272301099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124483211987200683514867399 186724817980801025272301099)
    ·
      refine ⟨280087226971201537908451649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186724817980801025272301099 280087226971201537908451649)
      ·
        refine ⟨210065420228401153431338737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280087226971201537908451649 210065420228401153431338737)
        ·
          refine ⟨157549065171300865073504053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210065420228401153431338737 157549065171300865073504053)
          ·
            refine ⟨14770224859809456100641005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157549065171300865073504053 14770224859809456100641005)
            ·
              refine ⟨5538834322428546037740377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14770224859809456100641005 5538834322428546037740377)
              ·
                refine ⟨4154125741821409528305283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5538834322428546037740377 4154125741821409528305283)
                ·
                  refine ⟨6231188612732114292457925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4154125741821409528305283 6231188612732114292457925)
                  ·
                    refine ⟨1168347864887271429835861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6231188612732114292457925 1168347864887271429835861)
                    ·
                      rfl

theorem cell23_6826048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 2, 1, 4].length) (baseStart_6826048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826048 prefixEnd_6826048 := by exact prefixLift 6826048
  have htrace : WordTrace (prefixWord ++ tailWord_6826048) baseStart_6826048 baseEnd_6826048 := by
    simpa [prefixWord, tailWord_6826048, baseEnd_6826048] using wordTrace_append hprefix tailTrace_6826048
  have hstable : (prefixWord ++ tailWord_6826048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826048).length < 2 ^ (prefixWord ++ tailWord_6826048).sum := by decide
  have hdescent : baseEnd_6826048 < baseStart_6826048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826057 : List Nat := [1, 2, 1, 1, 2, 2, 4, 2, 3, 5]
def baseStart_6826057 : Nat := 118140960795 + 6826057 * 2 ^ 59
def prefixEnd_6826057 : Nat := 4983230072969 + 3 ^ 40 * 6826057 * 2
def baseEnd_6826057 : Nat := 1168349405329234918098347

theorem tailTrace_6826057 : CollatzResearch.WordTrace tailWord_6826057 prefixEnd_6826057 1168349405329234918098347 := by
  unfold tailWord_6826057
  simp only [CollatzResearch.WordTrace]
  refine ⟨248966752231368761566812425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165977834820912507711208283 248966752231368761566812425)
  ·
    refine ⟨186725064173526571175109319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248966752231368761566812425 186725064173526571175109319)
    ·
      refine ⟨280087596260289856762663979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186725064173526571175109319 280087596260289856762663979)
      ·
        refine ⟨420131394390434785143995969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280087596260289856762663979 420131394390434785143995969)
        ·
          refine ⟨315098545792826088857996977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420131394390434785143995969 315098545792826088857996977)
          ·
            refine ⟨236323909344619566643497733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315098545792826088857996977 236323909344619566643497733)
            ·
              refine ⟨44310733002116168745655825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 236323909344619566643497733 44310733002116168745655825)
              ·
                refine ⟨33233049751587126559241869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44310733002116168745655825 33233049751587126559241869)
                ·
                  refine ⟨12462393656845172459715701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33233049751587126559241869 12462393656845172459715701)
                  ·
                    refine ⟨1168349405329234918098347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12462393656845172459715701 1168349405329234918098347)
                    ·
                      rfl

theorem cell23_6826057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 5].length) (baseStart_6826057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826057 prefixEnd_6826057 := by exact prefixLift 6826057
  have htrace : WordTrace (prefixWord ++ tailWord_6826057) baseStart_6826057 baseEnd_6826057 := by
    simpa [prefixWord, tailWord_6826057, baseEnd_6826057] using wordTrace_append hprefix tailTrace_6826057
  have hstable : (prefixWord ++ tailWord_6826057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826057).length < 2 ^ (prefixWord ++ tailWord_6826057).sum := by decide
  have hdescent : baseEnd_6826057 < baseStart_6826057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826105 : List Nat := [1, 2, 1, 3, 4, 1, 4, 2, 1, 1, 3]
def baseStart_6826105 : Nat := 118140960795 + 6826105 * 2 ^ 59
def prefixEnd_6826105 : Nat := 4983230072969 + 3 ^ 40 * 6826105 * 2
def baseEnd_6826105 : Nat := 3505072863059120566494821

theorem tailTrace_6826105 : CollatzResearch.WordTrace tailWord_6826105 prefixEnd_6826105 3505072863059120566494821 := by
  unfold tailWord_6826105
  simp only [CollatzResearch.WordTrace]
  refine ⟨248968502935194865764559769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165979001956796577176373179 248968502935194865764559769)
  ·
    refine ⟨186726377201396149323419827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248968502935194865764559769 186726377201396149323419827)
    ·
      refine ⟨280089565802094223985129741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186726377201396149323419827 280089565802094223985129741)
      ·
        refine ⟨105033587175785333994423653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280089565802094223985129741 105033587175785333994423653)
        ·
          refine ⟨19693797595459750123954435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105033587175785333994423653 19693797595459750123954435)
          ·
            refine ⟨29540696393189625185931653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19693797595459750123954435 29540696393189625185931653)
            ·
              refine ⟨5538880573723054722362185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29540696393189625185931653 5538880573723054722362185)
              ·
                refine ⟨4154160430292291041771639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5538880573723054722362185 4154160430292291041771639)
                ·
                  refine ⟨6231240645438436562657459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4154160430292291041771639 6231240645438436562657459)
                  ·
                    refine ⟨9346860968157654843986189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6231240645438436562657459 9346860968157654843986189)
                    ·
                      refine ⟨3505072863059120566494821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9346860968157654843986189 3505072863059120566494821)
                      ·
                        rfl

theorem cell23_6826105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 2, 1, 1, 3].length) (baseStart_6826105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826105 prefixEnd_6826105 := by exact prefixLift 6826105
  have htrace : WordTrace (prefixWord ++ tailWord_6826105) baseStart_6826105 baseEnd_6826105 := by
    simpa [prefixWord, tailWord_6826105, baseEnd_6826105] using wordTrace_append hprefix tailTrace_6826105
  have hstable : (prefixWord ++ tailWord_6826105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826105).length < 2 ^ (prefixWord ++ tailWord_6826105).sum := by decide
  have hdescent : baseEnd_6826105 < baseStart_6826105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826132 : List Nat := [2, 4, 2, 3, 1, 2, 1, 1, 2, 3, 2]
def baseStart_6826132 : Nat := 118140960795 + 6826132 * 2 ^ 59
def prefixEnd_6826132 : Nat := 4983230072969 + 3 ^ 40 * 6826132 * 2
def baseEnd_6826132 : Nat := 3505086727036791960857197

theorem tailTrace_6826132 : CollatzResearch.WordTrace tailWord_6826132 prefixEnd_6826132 3505086727036791960857197 := by
  unfold tailWord_6826132
  simp only [CollatzResearch.WordTrace]
  refine ⟨124484743853048524687896325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165979658470731366250528433 124484743853048524687896325)
  ·
    refine ⟨23340889472446598378980561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124484743853048524687896325 23340889472446598378980561)
    ·
      refine ⟨17505667104334948784235421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23340889472446598378980561 17505667104334948784235421)
      ·
        refine ⟨6564625164125605794088283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17505667104334948784235421 6564625164125605794088283)
        ·
          refine ⟨9846937746188408691132425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6564625164125605794088283 9846937746188408691132425)
          ·
            refine ⟨7385203309641306518349319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9846937746188408691132425 7385203309641306518349319)
            ·
              refine ⟨11077804964461959777523979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7385203309641306518349319 11077804964461959777523979)
              ·
                refine ⟨16616707446692939666285969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11077804964461959777523979 16616707446692939666285969)
                ·
                  refine ⟨12462530585019704749714477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16616707446692939666285969 12462530585019704749714477)
                  ·
                    refine ⟨4673448969382389281142929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12462530585019704749714477 4673448969382389281142929)
                    ·
                      refine ⟨3505086727036791960857197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4673448969382389281142929 3505086727036791960857197)
                      ·
                        rfl

theorem cell23_6826132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_6826132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826132 prefixEnd_6826132 := by exact prefixLift 6826132
  have htrace : WordTrace (prefixWord ++ tailWord_6826132) baseStart_6826132 baseEnd_6826132 := by
    simpa [prefixWord, tailWord_6826132, baseEnd_6826132] using wordTrace_append hprefix tailTrace_6826132
  have hstable : (prefixWord ++ tailWord_6826132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826132).length < 2 ^ (prefixWord ++ tailWord_6826132).sum := by decide
  have hdescent : baseEnd_6826132 < baseStart_6826132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826142 : List Nat := [4, 3, 1, 1, 4, 1, 2, 1, 1, 5]
def baseStart_6826142 : Nat := 118140960795 + 6826142 * 2 ^ 59
def prefixEnd_6826142 : Nat := 4983230072969 + 3 ^ 40 * 6826142 * 2
def baseEnd_6826142 : Nat := 1168363953947778973910717

theorem tailTrace_6826142 : CollatzResearch.WordTrace tailWord_6826142 prefixEnd_6826142 1168363953947778973910717 := by
  unfold tailWord_6826142
  simp only [CollatzResearch.WordTrace]
  refine ⟨31121231554507602635457085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165979901624040547389104453 31121231554507602635457085)
  ·
    refine ⟨11670461832940350988296407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31121231554507602635457085 11670461832940350988296407)
    ·
      refine ⟨17505692749410526482444611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11670461832940350988296407 17505692749410526482444611)
      ·
        refine ⟨26258539124115789723666917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17505692749410526482444611 26258539124115789723666917)
        ·
          refine ⟨4923476085771710573187547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26258539124115789723666917 4923476085771710573187547)
          ·
            refine ⟨7385214128657565859781321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4923476085771710573187547 7385214128657565859781321)
            ·
              refine ⟨5538910596493174394835991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7385214128657565859781321 5538910596493174394835991)
              ·
                refine ⟨8308365894739761592253987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5538910596493174394835991 8308365894739761592253987)
                ·
                  refine ⟨12462548842109642388380981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8308365894739761592253987 12462548842109642388380981)
                  ·
                    refine ⟨1168363953947778973910717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12462548842109642388380981 1168363953947778973910717)
                    ·
                      rfl

theorem cell23_6826142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_6826142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826142 prefixEnd_6826142 := by exact prefixLift 6826142
  have htrace : WordTrace (prefixWord ++ tailWord_6826142) baseStart_6826142 baseEnd_6826142 := by
    simpa [prefixWord, tailWord_6826142, baseEnd_6826142] using wordTrace_append hprefix tailTrace_6826142
  have hstable : (prefixWord ++ tailWord_6826142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826142).length < 2 ^ (prefixWord ++ tailWord_6826142).sum := by decide
  have hdescent : baseEnd_6826142 < baseStart_6826142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826145 : List Nat := [1, 2, 3, 3, 1, 2, 1, 5, 1, 2, 2]
def baseStart_6826145 : Nat := 118140960795 + 6826145 * 2 ^ 59
def prefixEnd_6826145 : Nat := 4983230072969 + 3 ^ 40 * 6826145 * 2
def baseEnd_6826145 : Nat := 3505093402285300409994637

theorem tailTrace_6826145 : CollatzResearch.WordTrace tailWord_6826145 prefixEnd_6826145 3505093402285300409994637 := by
  unfold tailWord_6826145
  simp only [CollatzResearch.WordTrace]
  refine ⟨248969961855049952596015889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165979974570033301730677259 248969961855049952596015889)
  ·
    refine ⟨186727471391287464447011917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248969961855049952596015889 186727471391287464447011917)
    ·
      refine ⟨70022801771732799167629469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186727471391287464447011917 70022801771732799167629469)
      ·
        refine ⟨26258550664399799687861051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70022801771732799167629469 26258550664399799687861051)
        ·
          refine ⟨39387825996599699531791577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26258550664399799687861051 39387825996599699531791577)
          ·
            refine ⟨29540869497449774648843683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39387825996599699531791577 29540869497449774648843683)
            ·
              refine ⟨44311304246174661973265525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29540869497449774648843683 44311304246174661973265525)
              ·
                refine ⟨4154184773078874559993643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44311304246174661973265525 4154184773078874559993643)
                ·
                  refine ⟨6231277159618311839990465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4154184773078874559993643 6231277159618311839990465)
                  ·
                    refine ⟨4673457869713733879992849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6231277159618311839990465 4673457869713733879992849)
                    ·
                      refine ⟨3505093402285300409994637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4673457869713733879992849 3505093402285300409994637)
                      ·
                        rfl

theorem cell23_6826145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_6826145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826145 prefixEnd_6826145 := by exact prefixLift 6826145
  have htrace : WordTrace (prefixWord ++ tailWord_6826145) baseStart_6826145 baseEnd_6826145 := by
    simpa [prefixWord, tailWord_6826145, baseEnd_6826145] using wordTrace_append hprefix tailTrace_6826145
  have hstable : (prefixWord ++ tailWord_6826145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826145).length < 2 ^ (prefixWord ++ tailWord_6826145).sum := by decide
  have hdescent : baseEnd_6826145 < baseStart_6826145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826148 : List Nat := [2, 3, 1, 2, 4, 1, 1, 3, 1, 2, 3]
def baseStart_6826148 : Nat := 118140960795 + 6826148 * 2 ^ 59
def prefixEnd_6826148 : Nat := 4983230072969 + 3 ^ 40 * 6826148 * 2
def baseEnd_6826148 : Nat := 3505094942727263898257123

theorem tailTrace_6826148 : CollatzResearch.WordTrace tailWord_6826148 prefixEnd_6826148 3505094942727263898257123 := by
  unfold tailWord_6826148
  simp only [CollatzResearch.WordTrace]
  refine ⟨124485035637019542054187549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165980047516026056072250065 124485035637019542054187549)
  ·
    refine ⟨46681888363882328270320331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124485035637019542054187549 46681888363882328270320331)
    ·
      refine ⟨70022832545823492405480497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46681888363882328270320331 70022832545823492405480497)
      ·
        refine ⟨52517124409367619304110373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70022832545823492405480497 52517124409367619304110373)
        ·
          refine ⟨9846960826756428619520695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52517124409367619304110373 9846960826756428619520695)
          ·
            refine ⟨14770441240134642929281043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9846960826756428619520695 14770441240134642929281043)
            ·
              refine ⟨22155661860201964393921565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14770441240134642929281043 22155661860201964393921565)
              ·
                refine ⟨8308373197575736647720587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22155661860201964393921565 8308373197575736647720587)
                ·
                  refine ⟨12462559796363604971580881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8308373197575736647720587 12462559796363604971580881)
                  ·
                    refine ⟨9346919847272703728685661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12462559796363604971580881 9346919847272703728685661)
                    ·
                      refine ⟨3505094942727263898257123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9346919847272703728685661 3505094942727263898257123)
                      ·
                        rfl

theorem cell23_6826148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_6826148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826148 prefixEnd_6826148 := by exact prefixLift 6826148
  have htrace : WordTrace (prefixWord ++ tailWord_6826148) baseStart_6826148 baseEnd_6826148 := by
    simpa [prefixWord, tailWord_6826148, baseEnd_6826148] using wordTrace_append hprefix tailTrace_6826148
  have hstable : (prefixWord ++ tailWord_6826148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826148).length < 2 ^ (prefixWord ++ tailWord_6826148).sum := by decide
  have hdescent : baseEnd_6826148 < baseStart_6826148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826201 : List Nat := [1, 2, 1, 2, 3, 1, 2, 4, 1, 4, 2]
def baseStart_6826201 : Nat := 118140960795 + 6826201 * 2 ^ 59
def prefixEnd_6826201 : Nat := 4983230072969 + 3 ^ 40 * 6826201 * 2
def baseEnd_6826201 : Nat := 3505122157201952190894379

theorem tailTrace_6826201 : CollatzResearch.WordTrace tailWord_6826201 prefixEnd_6826201 3505122157201952190894379 := by
  unfold tailWord_6826201
  simp only [CollatzResearch.WordTrace]
  refine ⟨248972004342847074160054457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165981336228564716106702971 248972004342847074160054457)
  ·
    refine ⟨186729003257135305620040843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248972004342847074160054457 186729003257135305620040843)
    ·
      refine ⟨280093504885702958430061265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186729003257135305620040843 280093504885702958430061265)
      ·
        refine ⟨210070128664277218822545949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280093504885702958430061265 210070128664277218822545949)
        ·
          refine ⟨78776298249103957058454731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210070128664277218822545949 78776298249103957058454731)
          ·
            refine ⟨118164447373655935587682097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78776298249103957058454731 118164447373655935587682097)
            ·
              refine ⟨88623335530241951690761573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118164447373655935587682097 88623335530241951690761573)
              ·
                refine ⟨16616875411920365942017795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88623335530241951690761573 16616875411920365942017795)
                ·
                  refine ⟨24925313117880548913026693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16616875411920365942017795 24925313117880548913026693)
                  ·
                    refine ⟨4673496209602602921192505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24925313117880548913026693 4673496209602602921192505)
                    ·
                      refine ⟨3505122157201952190894379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4673496209602602921192505 3505122157201952190894379)
                      ·
                        rfl

theorem cell23_6826201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 4, 2].length) (baseStart_6826201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826201 prefixEnd_6826201 := by exact prefixLift 6826201
  have htrace : WordTrace (prefixWord ++ tailWord_6826201) baseStart_6826201 baseEnd_6826201 := by
    simpa [prefixWord, tailWord_6826201, baseEnd_6826201] using wordTrace_append hprefix tailTrace_6826201
  have hstable : (prefixWord ++ tailWord_6826201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826201).length < 2 ^ (prefixWord ++ tailWord_6826201).sum := by decide
  have hdescent : baseEnd_6826201 < baseStart_6826201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826205 : List Nat := [1, 4, 3, 2, 1, 1, 2, 3, 1, 3, 2]
def baseStart_6826205 : Nat := 118140960795 + 6826205 * 2 ^ 59
def prefixEnd_6826205 : Nat := 4983230072969 + 3 ^ 40 * 6826205 * 2
def baseEnd_6826205 : Nat := 3505124211124570175244361

theorem tailTrace_6826205 : CollatzResearch.WordTrace tailWord_6826205 prefixEnd_6826205 3505124211124570175244361 := by
  unfold tailWord_6826205
  simp only [CollatzResearch.WordTrace]
  refine ⟨248972150234832582843200069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165981433489888388562133379 248972150234832582843200069)
  ·
    refine ⟨46682278169031109283100013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248972150234832582843200069 46682278169031109283100013)
    ·
      refine ⟨17505854313386665981162505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46682278169031109283100013 17505854313386665981162505)
      ·
        refine ⟨13129390735039999485871879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17505854313386665981162505 13129390735039999485871879)
        ·
          refine ⟨19694086102559999228807819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13129390735039999485871879 19694086102559999228807819)
          ·
            refine ⟨29541129153839998843211729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19694086102559999228807819 29541129153839998843211729)
            ·
              refine ⟨22155846865379999132408797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29541129153839998843211729 22155846865379999132408797)
              ·
                refine ⟨8308442574517499674653299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22155846865379999132408797 8308442574517499674653299)
                ·
                  refine ⟨12462663861776249511979949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8308442574517499674653299 12462663861776249511979949)
                  ·
                    refine ⟨4673498948166093566992481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12462663861776249511979949 4673498948166093566992481)
                    ·
                      refine ⟨3505124211124570175244361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4673498948166093566992481 3505124211124570175244361)
                      ·
                        rfl

theorem cell23_6826205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_6826205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826205 prefixEnd_6826205 := by exact prefixLift 6826205
  have htrace : WordTrace (prefixWord ++ tailWord_6826205) baseStart_6826205 baseEnd_6826205 := by
    simpa [prefixWord, tailWord_6826205, baseEnd_6826205] using wordTrace_append hprefix tailTrace_6826205
  have hstable : (prefixWord ++ tailWord_6826205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826205).length < 2 ^ (prefixWord ++ tailWord_6826205).sum := by decide
  have hdescent : baseEnd_6826205 < baseStart_6826205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826218 : List Nat := [3, 1, 3, 1, 1, 2, 1, 3, 4, 2, 2]
def baseStart_6826218 : Nat := 118140960795 + 6826218 * 2 ^ 59
def prefixEnd_6826218 : Nat := 4983230072969 + 3 ^ 40 * 6826218 * 2
def baseEnd_6826218 : Nat := 3505130886373078624381801

theorem tailTrace_6826218 : CollatzResearch.WordTrace tailWord_6826218 prefixEnd_6826218 3505130886373078624381801 := by
  unfold tailWord_6826218
  simp only [CollatzResearch.WordTrace]
  refine ⟨62243156095946371515855827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165981749589190324042282205 62243156095946371515855827)
  ·
    refine ⟨93364734143919557273783741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62243156095946371515855827 93364734143919557273783741)
    ·
      refine ⟨35011775303969833977668903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93364734143919557273783741 35011775303969833977668903)
      ·
        refine ⟨52517662955954750966503355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35011775303969833977668903 52517662955954750966503355)
        ·
          refine ⟨78776494433932126449755033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52517662955954750966503355 78776494433932126449755033)
          ·
            refine ⟨59082370825449094837316275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78776494433932126449755033 59082370825449094837316275)
            ·
              refine ⟨88623556238173642255974413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59082370825449094837316275 88623556238173642255974413)
              ·
                refine ⟨33233833589315115845990405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88623556238173642255974413 33233833589315115845990405)
                ·
                  refine ⟨6231343797996584221123201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33233833589315115845990405 6231343797996584221123201)
                  ·
                    refine ⟨4673507848497438165842401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6231343797996584221123201 4673507848497438165842401)
                    ·
                      refine ⟨3505130886373078624381801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4673507848497438165842401 3505130886373078624381801)
                      ·
                        rfl

theorem cell23_6826218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_6826218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826218 prefixEnd_6826218 := by exact prefixLift 6826218
  have htrace : WordTrace (prefixWord ++ tailWord_6826218) baseStart_6826218 baseEnd_6826218 := by
    simpa [prefixWord, tailWord_6826218, baseEnd_6826218] using wordTrace_append hprefix tailTrace_6826218
  have hstable : (prefixWord ++ tailWord_6826218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826218).length < 2 ^ (prefixWord ++ tailWord_6826218).sum := by decide
  have hdescent : baseEnd_6826218 < baseStart_6826218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826264 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 3, 2, 5]
def baseStart_6826264 : Nat := 118140960795 + 6826264 * 2 ^ 59
def prefixEnd_6826264 : Nat := 4983230072969 + 3 ^ 40 * 6826264 * 2
def baseEnd_6826264 : Nat := 3505154506483185444406589

theorem tailTrace_6826264 : CollatzResearch.WordTrace tailWord_6826264 prefixEnd_6826264 3505154506483185444406589 := by
  unfold tailWord_6826264
  simp only [CollatzResearch.WordTrace]
  refine ⟨124487151070809417959798923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165982868094412557279731897 124487151070809417959798923)
  ·
    refine ⟨186730726606214126939698385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124487151070809417959798923 186730726606214126939698385)
    ·
      refine ⟨140048044954660595204773789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186730726606214126939698385 140048044954660595204773789)
      ·
        refine ⟨52518016857997723201790171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140048044954660595204773789 52518016857997723201790171)
        ·
          refine ⟨78777025286996584802685257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52518016857997723201790171 78777025286996584802685257)
          ·
            refine ⟨59082768965247438602013943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78777025286996584802685257 59082768965247438602013943)
            ·
              refine ⟨88624153447871157903020915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59082768965247438602013943 88624153447871157903020915)
              ·
                refine ⟨132936230171806736854531373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88624153447871157903020915 132936230171806736854531373)
                ·
                  refine ⟨49851086314427526320449265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132936230171806736854531373 49851086314427526320449265)
                  ·
                    refine ⟨37388314735820644740336949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49851086314427526320449265 37388314735820644740336949)
                    ·
                      refine ⟨3505154506483185444406589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37388314735820644740336949 3505154506483185444406589)
                      ·
                        rfl

theorem cell23_6826264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_6826264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826264 prefixEnd_6826264 := by exact prefixLift 6826264
  have htrace : WordTrace (prefixWord ++ tailWord_6826264) baseStart_6826264 baseEnd_6826264 := by
    simpa [prefixWord, tailWord_6826264, baseEnd_6826264] using wordTrace_append hprefix tailTrace_6826264
  have hstable : (prefixWord ++ tailWord_6826264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826264).length < 2 ^ (prefixWord ++ tailWord_6826264).sum := by decide
  have hdescent : baseEnd_6826264 < baseStart_6826264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826271 : List Nat := [1, 1, 2, 4, 3, 1, 2, 2, 2, 5]
def baseStart_6826271 : Nat := 118140960795 + 6826271 * 2 ^ 59
def prefixEnd_6826271 : Nat := 4983230072969 + 3 ^ 40 * 6826271 * 2
def baseEnd_6826271 : Nat := 1168386033615922305673019

theorem tailTrace_6826271 : CollatzResearch.WordTrace tailWord_6826271 prefixEnd_6826271 1168386033615922305673019 := by
  unfold tailWord_6826271
  simp only [CollatzResearch.WordTrace]
  refine ⟨248974557452593476115102667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165983038301728984076735111 248974557452593476115102667)
  ·
    refine ⟨373461836178890214172654001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248974557452593476115102667 373461836178890214172654001)
    ·
      refine ⟨280096377134167660629490501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373461836178890214172654001 280096377134167660629490501)
      ·
        refine ⟨52518070712656436368029469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 280096377134167660629490501 52518070712656436368029469)
        ·
          refine ⟨19694276517246163638011051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52518070712656436368029469 19694276517246163638011051)
          ·
            refine ⟨29541414775869245457016577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19694276517246163638011051 29541414775869245457016577)
            ·
              refine ⟨22156061081901934092762433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29541414775869245457016577 22156061081901934092762433)
              ·
                refine ⟨16617045811426450569571825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22156061081901934092762433 16617045811426450569571825)
                ·
                  refine ⟨12462784358569837927178869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16617045811426450569571825 12462784358569837927178869)
                  ·
                    refine ⟨1168386033615922305673019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12462784358569837927178869 1168386033615922305673019)
                    ·
                      rfl

theorem cell23_6826271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 5].length) (baseStart_6826271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826271 prefixEnd_6826271 := by exact prefixLift 6826271
  have htrace : WordTrace (prefixWord ++ tailWord_6826271) baseStart_6826271 baseEnd_6826271 := by
    simpa [prefixWord, tailWord_6826271, baseEnd_6826271] using wordTrace_append hprefix tailTrace_6826271
  have hstable : (prefixWord ++ tailWord_6826271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826271).length < 2 ^ (prefixWord ++ tailWord_6826271).sum := by decide
  have hdescent : baseEnd_6826271 < baseStart_6826271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826285 : List Nat := [1, 5, 3, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_6826285 : Nat := 118140960795 + 6826285 * 2 ^ 59
def prefixEnd_6826285 : Nat := 4983230072969 + 3 ^ 40 * 6826285 * 2
def baseEnd_6826285 : Nat := 3505165289576929862243993

theorem tailTrace_6826285 : CollatzResearch.WordTrace tailWord_6826285 prefixEnd_6826285 3505165289576929862243993 := by
  unfold tailWord_6826285
  simp only [CollatzResearch.WordTrace]
  refine ⟨248975068074542756506112309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165983378716361837670741539 248975068074542756506112309)
  ·
    refine ⟨23341412631988383422448029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 248975068074542756506112309 23341412631988383422448029)
    ·
      refine ⟨8753029736995643783418011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23341412631988383422448029 8753029736995643783418011)
      ·
        refine ⟨13129544605493465675127017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8753029736995643783418011 13129544605493465675127017)
        ·
          refine ⟨9847158454120099256345263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13129544605493465675127017 9847158454120099256345263)
          ·
            refine ⟨14770737681180148884517895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9847158454120099256345263 14770737681180148884517895)
            ·
              refine ⟨22156106521770223326776843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14770737681180148884517895 22156106521770223326776843)
              ·
                refine ⟨33234159782655334990165265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22156106521770223326776843 33234159782655334990165265)
                ·
                  refine ⟨24925619836991501242623949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33234159782655334990165265 24925619836991501242623949)
                  ·
                    refine ⟨9347107438871812965983981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24925619836991501242623949 9347107438871812965983981)
                    ·
                      refine ⟨3505165289576929862243993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9347107438871812965983981 3505165289576929862243993)
                      ·
                        rfl

theorem cell23_6826285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_6826285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826285 prefixEnd_6826285 := by exact prefixLift 6826285
  have htrace : WordTrace (prefixWord ++ tailWord_6826285) baseStart_6826285 baseEnd_6826285 := by
    simpa [prefixWord, tailWord_6826285, baseEnd_6826285] using wordTrace_append hprefix tailTrace_6826285
  have hstable : (prefixWord ++ tailWord_6826285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826285).length < 2 ^ (prefixWord ++ tailWord_6826285).sum := by decide
  have hdescent : baseEnd_6826285 < baseStart_6826285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826304 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 4]
def baseStart_6826304 : Nat := 118140960795 + 6826304 * 2 ^ 59
def prefixEnd_6826304 : Nat := 4983230072969 + 3 ^ 40 * 6826304 * 2
def baseEnd_6826304 : Nat := 3505175045709365287906405

theorem tailTrace_6826304 : CollatzResearch.WordTrace tailWord_6826304 prefixEnd_6826304 3505175045709365287906405 := by
  unfold tailWord_6826304
  simp only [CollatzResearch.WordTrace]
  refine ⟨124487880530736961375526983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165983840707649281834035977 124487880530736961375526983)
  ·
    refine ⟨186731820796105442063290475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124487880530736961375526983 186731820796105442063290475)
    ·
      refine ⟨280097731194158163094935713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186731820796105442063290475 280097731194158163094935713)
      ·
        refine ⟨210073298395618622321201785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280097731194158163094935713 210073298395618622321201785)
        ·
          refine ⟨157554973796713966740901339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210073298395618622321201785 157554973796713966740901339)
          ·
            refine ⟨236332460695070950111352009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157554973796713966740901339 236332460695070950111352009)
            ·
              refine ⟨177249345521303212583514007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236332460695070950111352009 177249345521303212583514007)
              ·
                refine ⟨265874018281954818875271011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177249345521303212583514007 265874018281954818875271011)
                ·
                  refine ⟨398811027422932228312906517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265874018281954818875271011 398811027422932228312906517)
                  ·
                    refine ⟨18694266910449948202167493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 398811027422932228312906517 18694266910449948202167493)
                    ·
                      refine ⟨3505175045709365287906405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18694266910449948202167493 3505175045709365287906405)
                      ·
                        rfl

theorem cell23_6826304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_6826304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826304 prefixEnd_6826304 := by exact prefixLift 6826304
  have htrace : WordTrace (prefixWord ++ tailWord_6826304) baseStart_6826304 baseEnd_6826304 := by
    simpa [prefixWord, tailWord_6826304, baseEnd_6826304] using wordTrace_append hprefix tailTrace_6826304
  have hstable : (prefixWord ++ tailWord_6826304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826304).length < 2 ^ (prefixWord ++ tailWord_6826304).sum := by decide
  have hdescent : baseEnd_6826304 < baseStart_6826304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826305 : List Nat := [1, 2, 5, 2, 2, 2, 1, 1, 2, 5]
def baseStart_6826305 : Nat := 118140960795 + 6826305 * 2 ^ 59
def prefixEnd_6826305 : Nat := 4983230072969 + 3 ^ 40 * 6826305 * 2
def baseEnd_6826305 : Nat := 1168391853063339927997967

theorem tailTrace_6826305 : CollatzResearch.WordTrace tailWord_6826305 prefixEnd_6826305 1168391853063339927997967 := by
  unfold tailWord_6826305
  simp only [CollatzResearch.WordTrace]
  refine ⟨248975797534470299921840369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165983865022980199947893579 248975797534470299921840369)
  ·
    refine ⟨186731848150852724941380277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248975797534470299921840369 186731848150852724941380277)
    ·
      refine ⟨17506110764142442963254401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 186731848150852724941380277 17506110764142442963254401)
      ·
        refine ⟨13129583073106832222440801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17506110764142442963254401 13129583073106832222440801)
        ·
          refine ⟨9847187304830124166830601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13129583073106832222440801 9847187304830124166830601)
          ·
            refine ⟨7385390478622593125122951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9847187304830124166830601 7385390478622593125122951)
            ·
              refine ⟨11078085717933889687684427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7385390478622593125122951 11078085717933889687684427)
              ·
                refine ⟨16617128576900834531526641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11078085717933889687684427 16617128576900834531526641)
                ·
                  refine ⟨12462846432675625898644981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16617128576900834531526641 12462846432675625898644981)
                  ·
                    refine ⟨1168391853063339927997967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12462846432675625898644981 1168391853063339927997967)
                    ·
                      rfl

theorem cell23_6826305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_6826305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826305 prefixEnd_6826305 := by exact prefixLift 6826305
  have htrace : WordTrace (prefixWord ++ tailWord_6826305) baseStart_6826305 baseEnd_6826305 := by
    simpa [prefixWord, tailWord_6826305, baseEnd_6826305] using wordTrace_append hprefix tailTrace_6826305
  have hstable : (prefixWord ++ tailWord_6826305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826305).length < 2 ^ (prefixWord ++ tailWord_6826305).sum := by decide
  have hdescent : baseEnd_6826305 < baseStart_6826305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826311 : List Nat := [1, 1, 4, 1, 2, 2, 3, 1, 1, 4, 3]
def baseStart_6826311 : Nat := 118140960795 + 6826311 * 2 ^ 59
def prefixEnd_6826311 : Nat := 4983230072969 + 3 ^ 40 * 6826311 * 2
def baseEnd_6826311 : Nat := 3505178640073946760518873

theorem tailTrace_6826311 : CollatzResearch.WordTrace tailWord_6826311 prefixEnd_6826311 3505178640073946760518873 := by
  unfold tailWord_6826311
  simp only [CollatzResearch.WordTrace]
  refine ⟨248976016372448562946558787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165984010914965708631039191 248976016372448562946558787)
  ·
    refine ⟨373464024558672844419838181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248976016372448562946558787 373464024558672844419838181)
    ·
      refine ⟨70024504604751158328719659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 373464024558672844419838181 70024504604751158328719659)
      ·
        refine ⟨105036756907126737493079489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70024504604751158328719659 105036756907126737493079489)
        ·
          refine ⟨78777567680345053119809617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105036756907126737493079489 78777567680345053119809617)
          ·
            refine ⟨59083175760258789839857213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78777567680345053119809617 59083175760258789839857213)
            ·
              refine ⟨22156190910097046189946455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59083175760258789839857213 22156190910097046189946455)
              ·
                refine ⟨33234286365145569284919683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22156190910097046189946455 33234286365145569284919683)
                ·
                  refine ⟨49851429547718353927379525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33234286365145569284919683 49851429547718353927379525)
                  ·
                    refine ⟨9347143040197191361383661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49851429547718353927379525 9347143040197191361383661)
                    ·
                      refine ⟨3505178640073946760518873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9347143040197191361383661 3505178640073946760518873)
                      ·
                        rfl

theorem cell23_6826311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_6826311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826311 prefixEnd_6826311 := by exact prefixLift 6826311
  have htrace : WordTrace (prefixWord ++ tailWord_6826311) baseStart_6826311 baseEnd_6826311 := by
    simpa [prefixWord, tailWord_6826311, baseEnd_6826311] using wordTrace_append hprefix tailTrace_6826311
  have hstable : (prefixWord ++ tailWord_6826311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826311).length < 2 ^ (prefixWord ++ tailWord_6826311).sum := by decide
  have hdescent : baseEnd_6826311 < baseStart_6826311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826392 : List Nat := [2, 1, 2, 5, 1, 3, 1, 1, 3, 1, 3]
def baseStart_6826392 : Nat := 118140960795 + 6826392 * 2 ^ 59
def prefixEnd_6826392 : Nat := 4983230072969 + 3 ^ 40 * 6826392 * 2
def baseEnd_6826392 : Nat := 3505220232006960943606001

theorem tailTrace_6826392 : CollatzResearch.WordTrace tailWord_6826392 prefixEnd_6826392 3505220232006960943606001 := by
  unfold tailWord_6826392
  simp only [CollatzResearch.WordTrace]
  refine ⟨124489485342577556890128715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165985980456770075853504953 124489485342577556890128715)
  ·
    refine ⟨186734228013866335335193073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124489485342577556890128715 186734228013866335335193073)
    ·
      refine ⟨140050671010399751501394805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186734228013866335335193073 140050671010399751501394805)
      ·
        refine ⟨13129750407224976703255763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140050671010399751501394805 13129750407224976703255763)
        ·
          refine ⟨19694625610837465054883645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13129750407224976703255763 19694625610837465054883645)
          ·
            refine ⟨7385484604064049395581367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19694625610837465054883645 7385484604064049395581367)
            ·
              refine ⟨11078226906096074093372051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7385484604064049395581367 11078226906096074093372051)
              ·
                refine ⟨16617340359144111140058077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11078226906096074093372051 16617340359144111140058077)
                ·
                  refine ⟨6231502634679041677521779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16617340359144111140058077 6231502634679041677521779)
                  ·
                    refine ⟨9347253952018562516282669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6231502634679041677521779 9347253952018562516282669)
                    ·
                      refine ⟨3505220232006960943606001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9347253952018562516282669 3505220232006960943606001)
                      ·
                        rfl

theorem cell23_6826392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_6826392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826392 prefixEnd_6826392 := by exact prefixLift 6826392
  have htrace : WordTrace (prefixWord ++ tailWord_6826392) baseStart_6826392 baseEnd_6826392 := by
    simpa [prefixWord, tailWord_6826392, baseEnd_6826392] using wordTrace_append hprefix tailTrace_6826392
  have hstable : (prefixWord ++ tailWord_6826392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826392).length < 2 ^ (prefixWord ++ tailWord_6826392).sum := by decide
  have hdescent : baseEnd_6826392 < baseStart_6826392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826418 : List Nat := [3, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3]
def baseStart_6826418 : Nat := 118140960795 + 6826418 * 2 ^ 59
def prefixEnd_6826418 : Nat := 4983230072969 + 3 ^ 40 * 6826418 * 2
def baseEnd_6826418 : Nat := 3505233582503977841880881

theorem tailTrace_6826418 : CollatzResearch.WordTrace tailWord_6826418 prefixEnd_6826418 3505233582503977841880881 := by
  unfold tailWord_6826418
  simp only [CollatzResearch.WordTrace]
  refine ⟨62244979745765230055175977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165986612655373946813802605 62244979745765230055175977)
  ·
    refine ⟨46683734809323922541381983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62244979745765230055175977 46683734809323922541381983)
    ·
      refine ⟨70025602213985883812072975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46683734809323922541381983 70025602213985883812072975)
      ·
        refine ⟨105038403320978825718109463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70025602213985883812072975 105038403320978825718109463)
        ·
          refine ⟨157557604981468238577164195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105038403320978825718109463 157557604981468238577164195)
          ·
            refine ⟨236336407472202357865746293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157557604981468238577164195 236336407472202357865746293)
            ·
              refine ⟨22156538200518971049913715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 236336407472202357865746293 22156538200518971049913715)
              ·
                refine ⟨33234807300778456574870573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22156538200518971049913715 33234807300778456574870573)
                ·
                  refine ⟨12463052737791921215576465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33234807300778456574870573 12463052737791921215576465)
                  ·
                    refine ⟨9347289553343940911682349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12463052737791921215576465 9347289553343940911682349)
                    ·
                      refine ⟨3505233582503977841880881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9347289553343940911682349 3505233582503977841880881)
                      ·
                        rfl

theorem cell23_6826418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_6826418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826418 prefixEnd_6826418 := by exact prefixLift 6826418
  have htrace : WordTrace (prefixWord ++ tailWord_6826418) baseStart_6826418 baseEnd_6826418 := by
    simpa [prefixWord, tailWord_6826418, baseEnd_6826418] using wordTrace_append hprefix tailTrace_6826418
  have hstable : (prefixWord ++ tailWord_6826418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826418).length < 2 ^ (prefixWord ++ tailWord_6826418).sum := by decide
  have hdescent : baseEnd_6826418 < baseStart_6826418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826428 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 3, 2, 4]
def baseStart_6826428 : Nat := 118140960795 + 6826428 * 2 ^ 59
def prefixEnd_6826428 : Nat := 4983230072969 + 3 ^ 40 * 6826428 * 2
def baseEnd_6826428 : Nat := 3505238717310522802755835

theorem tailTrace_6826428 : CollatzResearch.WordTrace tailWord_6826428 prefixEnd_6826428 3505238717310522802755835 := by
  unfold tailWord_6826428
  simp only [CollatzResearch.WordTrace]
  refine ⟨124490141856512345964283969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165986855808683127952378625 124490141856512345964283969)
  ·
    refine ⟨93367606392384259473212977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124490141856512345964283969 93367606392384259473212977)
    ·
      refine ⟨70025704794288194604909733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93367606392384259473212977 70025704794288194604909733)
      ·
        refine ⟨13129819648929036488420575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70025704794288194604909733 13129819648929036488420575)
        ·
          refine ⟨19694729473393554732630863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13129819648929036488420575 19694729473393554732630863)
          ·
            refine ⟨29542094210090332098946295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19694729473393554732630863 29542094210090332098946295)
            ·
              refine ⟨44313141315135498148419443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29542094210090332098946295 44313141315135498148419443)
              ·
                refine ⟨66469711972703247222629165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44313141315135498148419443 66469711972703247222629165)
                ·
                  refine ⟨24926141989763717708485937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66469711972703247222629165 24926141989763717708485937)
                  ·
                    refine ⟨18694606492322788281364453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24926141989763717708485937 18694606492322788281364453)
                    ·
                      refine ⟨3505238717310522802755835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18694606492322788281364453 3505238717310522802755835)
                      ·
                        rfl

theorem cell23_6826428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_6826428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826428 prefixEnd_6826428 := by exact prefixLift 6826428
  have htrace : WordTrace (prefixWord ++ tailWord_6826428) baseStart_6826428 baseEnd_6826428 := by
    simpa [prefixWord, tailWord_6826428, baseEnd_6826428] using wordTrace_append hprefix tailTrace_6826428
  have hstable : (prefixWord ++ tailWord_6826428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826428).length < 2 ^ (prefixWord ++ tailWord_6826428).sum := by decide
  have hdescent : baseEnd_6826428 < baseStart_6826428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826432 : List Nat := [2, 1, 1, 2, 3, 1, 1, 7, 1, 2, 2]
def baseStart_6826432 : Nat := 118140960795 + 6826432 * 2 ^ 59
def prefixEnd_6826432 : Nat := 4983230072969 + 3 ^ 40 * 6826432 * 2
def baseEnd_6826432 : Nat := 3505240771233140787105817

theorem tailTrace_6826432 : CollatzResearch.WordTrace tailWord_6826432 prefixEnd_6826432 3505240771233140787105817 := by
  unfold tailWord_6826432
  simp only [CollatzResearch.WordTrace]
  refine ⟨124490214802505100305856775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165986953070006800407809033 124490214802505100305856775)
  ·
    refine ⟨186735322203757650458785163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124490214802505100305856775 186735322203757650458785163)
    ·
      refine ⟨280102983305636475688177745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186735322203757650458785163 280102983305636475688177745)
      ·
        refine ⟨210077237479227356766133309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280102983305636475688177745 210077237479227356766133309)
        ·
          refine ⟨78778964054710258787299991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210077237479227356766133309 78778964054710258787299991)
          ·
            refine ⟨118168446082065388180949987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78778964054710258787299991 118168446082065388180949987)
            ·
              refine ⟨177252669123098082271424981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118168446082065388180949987 177252669123098082271424981)
              ·
                refine ⟨4154359432572611303236523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 177252669123098082271424981 4154359432572611303236523)
                ·
                  refine ⟨6231539148858916954854785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4154359432572611303236523 6231539148858916954854785)
                  ·
                    refine ⟨4673654361644187716141089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6231539148858916954854785 4673654361644187716141089)
                    ·
                      refine ⟨3505240771233140787105817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4673654361644187716141089 3505240771233140787105817)
                      ·
                        rfl

theorem cell23_6826432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 7, 1, 2, 2].length) (baseStart_6826432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826432 prefixEnd_6826432 := by exact prefixLift 6826432
  have htrace : WordTrace (prefixWord ++ tailWord_6826432) baseStart_6826432 baseEnd_6826432 := by
    simpa [prefixWord, tailWord_6826432, baseEnd_6826432] using wordTrace_append hprefix tailTrace_6826432
  have hstable : (prefixWord ++ tailWord_6826432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826432).length < 2 ^ (prefixWord ++ tailWord_6826432).sum := by decide
  have hdescent : baseEnd_6826432 < baseStart_6826432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826465 : List Nat := [1, 2, 3, 1, 2, 2, 1, 5, 2, 1, 3]
def baseStart_6826465 : Nat := 118140960795 + 6826465 * 2 ^ 59
def prefixEnd_6826465 : Nat := 4983230072969 + 3 ^ 40 * 6826465 * 2
def baseEnd_6826465 : Nat := 3505257716094739157993165

theorem tailTrace_6826465 : CollatzResearch.WordTrace tailWord_6826465 prefixEnd_6826465 3505257716094739157993165 := by
  unfold tailWord_6826465
  simp only [CollatzResearch.WordTrace]
  refine ⟨248981633213890647247664849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165987755475927098165109899 248981633213890647247664849)
  ·
    refine ⟨186736224910417985435748637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248981633213890647247664849 186736224910417985435748637)
    ·
      refine ⟨70026084341406744538405739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186736224910417985435748637 70026084341406744538405739)
      ·
        refine ⟨105039126512110116807608609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70026084341406744538405739 105039126512110116807608609)
        ·
          refine ⟨78779344884082587605706457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105039126512110116807608609 78779344884082587605706457)
          ·
            refine ⟨59084508663061940704279843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78779344884082587605706457 59084508663061940704279843)
            ·
              refine ⟨88626762994592911056419765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59084508663061940704279843 88626762994592911056419765)
              ·
                refine ⟨8308759030743085411539353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88626762994592911056419765 8308759030743085411539353)
                ·
                  refine ⟨6231569273057314058654515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8308759030743085411539353 6231569273057314058654515)
                  ·
                    refine ⟨9347353909585971087981773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6231569273057314058654515 9347353909585971087981773)
                    ·
                      refine ⟨3505257716094739157993165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9347353909585971087981773 3505257716094739157993165)
                      ·
                        rfl

theorem cell23_6826465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_6826465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826465 prefixEnd_6826465 := by exact prefixLift 6826465
  have htrace : WordTrace (prefixWord ++ tailWord_6826465) baseStart_6826465 baseEnd_6826465 := by
    simpa [prefixWord, tailWord_6826465, baseEnd_6826465] using wordTrace_append hprefix tailTrace_6826465
  have hstable : (prefixWord ++ tailWord_6826465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826465).length < 2 ^ (prefixWord ++ tailWord_6826465).sum := by decide
  have hdescent : baseEnd_6826465 < baseStart_6826465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826466 : List Nat := [3, 3, 3, 2, 1, 1, 1, 2, 3, 2, 2]
def baseStart_6826466 : Nat := 118140960795 + 6826466 * 2 ^ 59
def prefixEnd_6826466 : Nat := 4983230072969 + 3 ^ 40 * 6826466 * 2
def baseEnd_6826466 : Nat := 3505258229575393654080661

theorem tailTrace_6826466 : CollatzResearch.WordTrace tailWord_6826466 prefixEnd_6826466 3505258229575393654080661 := by
  unfold tailWord_6826466
  simp only [CollatzResearch.WordTrace]
  refine ⟨62245417421721756104612813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165987779791258016278967501 62245417421721756104612813)
  ·
    refine ⟨23342031533145658539229805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62245417421721756104612813 23342031533145658539229805)
    ·
      refine ⟨8753261824929621952211177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23342031533145658539229805 8753261824929621952211177)
      ·
        refine ⟨6564946368697216464158383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8753261824929621952211177 6564946368697216464158383)
        ·
          refine ⟨9847419553045824696237575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6564946368697216464158383 9847419553045824696237575)
          ·
            refine ⟨14771129329568737044356363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9847419553045824696237575 14771129329568737044356363)
            ·
              refine ⟨22156693994353105566534545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14771129329568737044356363 22156693994353105566534545)
              ·
                refine ⟨16617520495764829174900909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22156693994353105566534545 16617520495764829174900909)
                ·
                  refine ⟨6231570185911810940587841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16617520495764829174900909 6231570185911810940587841)
                  ·
                    refine ⟨4673677639433858205440881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6231570185911810940587841 4673677639433858205440881)
                    ·
                      refine ⟨3505258229575393654080661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4673677639433858205440881 3505258229575393654080661)
                      ·
                        rfl

theorem cell23_6826466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_6826466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826466 prefixEnd_6826466 := by exact prefixLift 6826466
  have htrace : WordTrace (prefixWord ++ tailWord_6826466) baseStart_6826466 baseEnd_6826466 := by
    simpa [prefixWord, tailWord_6826466, baseEnd_6826466] using wordTrace_append hprefix tailTrace_6826466
  have hstable : (prefixWord ++ tailWord_6826466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826466).length < 2 ^ (prefixWord ++ tailWord_6826466).sum := by decide
  have hdescent : baseEnd_6826466 < baseStart_6826466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826475 : List Nat := [1, 1, 1, 1, 2, 3, 4, 4, 1, 3, 2]
def baseStart_6826475 : Nat := 118140960795 + 6826475 * 2 ^ 59
def prefixEnd_6826475 : Nat := 4983230072969 + 3 ^ 40 * 6826475 * 2
def baseEnd_6826475 : Nat := 3505262850901284118868119

theorem tailTrace_6826475 : CollatzResearch.WordTrace tailWord_6826475 prefixEnd_6826475 3505262850901284118868119 := by
  unfold tailWord_6826475
  simp only [CollatzResearch.WordTrace]
  refine ⟨248981997943854418955528879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165987998629236279303685919 248981997943854418955528879)
  ·
    refine ⟨373472996915781628433293319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248981997943854418955528879 373472996915781628433293319)
    ·
      refine ⟨560209495373672442649939979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373472996915781628433293319 560209495373672442649939979)
      ·
        refine ⟨840314243060508663974909969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560209495373672442649939979 840314243060508663974909969)
        ·
          refine ⟨630235682295381497981182477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 840314243060508663974909969 630235682295381497981182477)
          ·
            refine ⟨236338380860768061742943429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 630235682295381497981182477 236338380860768061742943429)
            ·
              refine ⟨44313446411394011576801893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 236338380860768061742943429 44313446411394011576801893)
              ·
                refine ⟨8308771202136377170650355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44313446411394011576801893 8308771202136377170650355)
                ·
                  refine ⟨12463156803204565755975533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8308771202136377170650355 12463156803204565755975533)
                  ·
                    refine ⟨4673683801201712158490825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12463156803204565755975533 4673683801201712158490825)
                    ·
                      refine ⟨3505262850901284118868119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4673683801201712158490825 3505262850901284118868119)
                      ·
                        rfl

theorem cell23_6826475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 3, 2].length) (baseStart_6826475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826475 prefixEnd_6826475 := by exact prefixLift 6826475
  have htrace : WordTrace (prefixWord ++ tailWord_6826475) baseStart_6826475 baseEnd_6826475 := by
    simpa [prefixWord, tailWord_6826475, baseEnd_6826475] using wordTrace_append hprefix tailTrace_6826475
  have hstable : (prefixWord ++ tailWord_6826475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826475).length < 2 ^ (prefixWord ++ tailWord_6826475).sum := by decide
  have hdescent : baseEnd_6826475 < baseStart_6826475 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826481 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 1, 8]
def baseStart_6826481 : Nat := 118140960795 + 6826481 * 2 ^ 59
def prefixEnd_6826481 : Nat := 4983230072969 + 3 ^ 40 * 6826481 * 2
def baseEnd_6826481 : Nat := 1168421977261737031797697

theorem tailTrace_6826481 : CollatzResearch.WordTrace tailWord_6826481 prefixEnd_6826481 1168421977261737031797697 := by
  unfold tailWord_6826481
  simp only [CollatzResearch.WordTrace]
  refine ⟨248982216781832681980247297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165988144521221787986831531 248982216781832681980247297)
  ·
    refine ⟨186736662586374511485185473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248982216781832681980247297 186736662586374511485185473)
    ·
      refine ⟨140052496939780883613889105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186736662586374511485185473 140052496939780883613889105)
      ·
        refine ⟨105039372704835662710416829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140052496939780883613889105 105039372704835662710416829)
        ·
          refine ⟨39389764764313373516406311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105039372704835662710416829 39389764764313373516406311)
          ·
            refine ⟨59084647146470060274609467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39389764764313373516406311 59084647146470060274609467)
            ·
              refine ⟨88626970719705090411914201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59084647146470060274609467 88626970719705090411914201)
              ·
                refine ⟨66470228039778817808935651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88626970719705090411914201 66470228039778817808935651)
                ·
                  refine ⟨99705342059668226713403477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66470228039778817808935651 99705342059668226713403477)
                  ·
                    refine ⟨1168421977261737031797697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 99705342059668226713403477 1168421977261737031797697)
                    ·
                      rfl

theorem cell23_6826481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 8].length) (baseStart_6826481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826481 prefixEnd_6826481 := by exact prefixLift 6826481
  have htrace : WordTrace (prefixWord ++ tailWord_6826481) baseStart_6826481 baseEnd_6826481 := by
    simpa [prefixWord, tailWord_6826481, baseEnd_6826481] using wordTrace_append hprefix tailTrace_6826481
  have hstable : (prefixWord ++ tailWord_6826481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826481).length < 2 ^ (prefixWord ++ tailWord_6826481).sum := by decide
  have hdescent : baseEnd_6826481 < baseStart_6826481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826511 : List Nat := [1, 1, 2, 1, 1, 1, 2, 7, 7]
def baseStart_6826511 : Nat := 118140960795 + 6826511 * 2 ^ 59
def prefixEnd_6826511 : Nat := 4983230072969 + 3 ^ 40 * 6826511 * 2
def baseEnd_6826511 : Nat := 389475704022760664224217

theorem tailTrace_6826511 : CollatzResearch.WordTrace tailWord_6826511 prefixEnd_6826511 389475704022760664224217 := by
  unfold tailWord_6826511
  simp only [CollatzResearch.WordTrace]
  refine ⟨248983310971723997103839387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165988873981149331402559591 248983310971723997103839387)
  ·
    refine ⟨373474966457585995655759081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248983310971723997103839387 373474966457585995655759081)
    ·
      refine ⟨280106224843189496741819311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373474966457585995655759081 280106224843189496741819311)
      ·
        refine ⟨420159337264784245112728967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280106224843189496741819311 420159337264784245112728967)
        ·
          refine ⟨630239005897176367669093451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420159337264784245112728967 630239005897176367669093451)
          ·
            refine ⟨945358508845764551503640177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630239005897176367669093451 945358508845764551503640177)
            ·
              refine ⟨709018881634323413627730133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 945358508845764551503640177 709018881634323413627730133)
              ·
                refine ⟨16617630038304455006899925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 709018881634323413627730133 16617630038304455006899925)
                ·
                  refine ⟨389475704022760664224217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16617630038304455006899925 389475704022760664224217)
                  ·
                    rfl

theorem cell23_6826511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 7].length) (baseStart_6826511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826511 prefixEnd_6826511 := by exact prefixLift 6826511
  have htrace : WordTrace (prefixWord ++ tailWord_6826511) baseStart_6826511 baseEnd_6826511 := by
    simpa [prefixWord, tailWord_6826511, baseEnd_6826511] using wordTrace_append hprefix tailTrace_6826511
  have hstable : (prefixWord ++ tailWord_6826511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826511).length < 2 ^ (prefixWord ++ tailWord_6826511).sum := by decide
  have hdescent : baseEnd_6826511 < baseStart_6826511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826516 : List Nat := [2, 4, 3, 1, 1, 2, 3, 1, 2, 1, 3]
def baseStart_6826516 : Nat := 118140960795 + 6826516 * 2 ^ 59
def prefixEnd_6826516 : Nat := 4983230072969 + 3 ^ 40 * 6826516 * 2
def baseEnd_6826516 : Nat := 3505283903608118458455431

theorem tailTrace_6826516 : CollatzResearch.WordTrace tailWord_6826516 prefixEnd_6826516 3505283903608118458455431 := by
  unfold tailWord_6826516
  simp only [CollatzResearch.WordTrace]
  refine ⟨124491746668352941478885701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165988995557803921971847601 124491746668352941478885701)
  ·
    refine ⟨23342202500316176527291069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124491746668352941478885701 23342202500316176527291069)
    ·
      refine ⟨8753325937618566197734151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23342202500316176527291069 8753325937618566197734151)
      ·
        refine ⟨13129988906427849296601227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8753325937618566197734151 13129988906427849296601227)
        ·
          refine ⟨19694983359641773944901841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13129988906427849296601227 19694983359641773944901841)
          ·
            refine ⟨14771237519731330458676381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19694983359641773944901841 14771237519731330458676381)
            ·
              refine ⟨5539214069899248922003643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14771237519731330458676381 5539214069899248922003643)
              ·
                refine ⟨8308821104848873383005465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5539214069899248922003643 8308821104848873383005465)
                ·
                  refine ⟨6231615828636655037254099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8308821104848873383005465 6231615828636655037254099)
                  ·
                    refine ⟨9347423742954982555881149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6231615828636655037254099 9347423742954982555881149)
                    ·
                      refine ⟨3505283903608118458455431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9347423742954982555881149 3505283903608118458455431)
                      ·
                        rfl

theorem cell23_6826516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_6826516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826516 prefixEnd_6826516 := by exact prefixLift 6826516
  have htrace : WordTrace (prefixWord ++ tailWord_6826516) baseStart_6826516 baseEnd_6826516 := by
    simpa [prefixWord, tailWord_6826516, baseEnd_6826516] using wordTrace_append hprefix tailTrace_6826516
  have hstable : (prefixWord ++ tailWord_6826516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826516).length < 2 ^ (prefixWord ++ tailWord_6826516).sum := by decide
  have hdescent : baseEnd_6826516 < baseStart_6826516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826522 : List Nat := [3, 1, 1, 3, 1, 1, 2, 5, 2, 2, 2]
def baseStart_6826522 : Nat := 118140960795 + 6826522 * 2 ^ 59
def prefixEnd_6826522 : Nat := 4983230072969 + 3 ^ 40 * 6826522 * 2
def baseEnd_6826522 : Nat := 3505286984492045434980403

theorem tailTrace_6826522 : CollatzResearch.WordTrace tailWord_6826522 prefixEnd_6826522 3505286984492045434980403 := by
  unfold tailWord_6826522
  simp only [CollatzResearch.WordTrace]
  refine ⟨62245928043671036495622455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165989141449789430654993213 62245928043671036495622455)
  ·
    refine ⟨93368892065506554743433683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62245928043671036495622455 93368892065506554743433683)
    ·
      refine ⟨140053338098259832115150525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93368892065506554743433683 140053338098259832115150525)
      ·
        refine ⟨52520001786847437043181447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140053338098259832115150525 52520001786847437043181447)
        ·
          refine ⟨78780002680271155564772171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52520001786847437043181447 78780002680271155564772171)
          ·
            refine ⟨118170004020406733347158257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78780002680271155564772171 118170004020406733347158257)
            ·
              refine ⟨88627503015305050010368693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118170004020406733347158257 88627503015305050010368693)
              ·
                refine ⟨8308828407684848438472065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88627503015305050010368693 8308828407684848438472065)
                ·
                  refine ⟨6231621305763636328854049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8308828407684848438472065 6231621305763636328854049)
                  ·
                    refine ⟨4673715979322727246640537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6231621305763636328854049 4673715979322727246640537)
                    ·
                      refine ⟨3505286984492045434980403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4673715979322727246640537 3505286984492045434980403)
                      ·
                        rfl

theorem cell23_6826522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_6826522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826522 prefixEnd_6826522 := by exact prefixLift 6826522
  have htrace : WordTrace (prefixWord ++ tailWord_6826522) baseStart_6826522 baseEnd_6826522 := by
    simpa [prefixWord, tailWord_6826522, baseEnd_6826522] using wordTrace_append hprefix tailTrace_6826522
  have hstable : (prefixWord ++ tailWord_6826522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826522).length < 2 ^ (prefixWord ++ tailWord_6826522).sum := by decide
  have hdescent : baseEnd_6826522 < baseStart_6826522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826545 : List Nat := [1, 2, 2, 3, 1, 1, 5, 3, 5]
def baseStart_6826545 : Nat := 118140960795 + 6826545 * 2 ^ 59
def prefixEnd_6826545 : Nat := 4983230072969 + 3 ^ 40 * 6826545 * 2
def baseEnd_6826545 : Nat := 389477643838566538332533

theorem tailTrace_6826545 : CollatzResearch.WordTrace tailWord_6826545 prefixEnd_6826545 389477643838566538332533 := by
  unfold tailWord_6826545
  simp only [CollatzResearch.WordTrace]
  refine ⟨248984551053600820910577089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165989700702400547273718059 248984551053600820910577089)
  ·
    refine ⟨186738413290200615682932817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248984551053600820910577089 186738413290200615682932817)
    ·
      refine ⟨140053809967650461762199613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186738413290200615682932817 140053809967650461762199613)
      ·
        refine ⟨52520178737868923160824855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140053809967650461762199613 52520178737868923160824855)
        ·
          refine ⟨78780268106803384741237283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52520178737868923160824855 78780268106803384741237283)
          ·
            refine ⟨118170402160205077111855925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78780268106803384741237283 118170402160205077111855925)
            ·
              refine ⟨11078475202519225979236493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118170402160205077111855925 11078475202519225979236493)
              ·
                refine ⟨4154428200944709742213685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11078475202519225979236493 4154428200944709742213685)
                ·
                  refine ⟨389477643838566538332533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4154428200944709742213685 389477643838566538332533)
                  ·
                    rfl

theorem cell23_6826545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 3, 5].length) (baseStart_6826545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826545 prefixEnd_6826545 := by exact prefixLift 6826545
  have htrace : WordTrace (prefixWord ++ tailWord_6826545) baseStart_6826545 baseEnd_6826545 := by
    simpa [prefixWord, tailWord_6826545, baseEnd_6826545] using wordTrace_append hprefix tailTrace_6826545
  have hstable : (prefixWord ++ tailWord_6826545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826545).length < 2 ^ (prefixWord ++ tailWord_6826545).sum := by decide
  have hdescent : baseEnd_6826545 < baseStart_6826545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826573 : List Nat := [1, 6, 1, 1, 2, 3, 2, 1, 2, 2, 2]
def baseStart_6826573 : Nat := 118140960795 + 6826573 * 2 ^ 59
def prefixEnd_6826573 : Nat := 4983230072969 + 3 ^ 40 * 6826573 * 2
def baseEnd_6826573 : Nat := 3505313172005424735442669

theorem tailTrace_6826573 : CollatzResearch.WordTrace tailWord_6826573 prefixEnd_6826573 3505313172005424735442669 := by
  unfold tailWord_6826573
  simp only [CollatzResearch.WordTrace]
  refine ⟨248985572297499381692596373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165990381531666254461730915 248985572297499381692596373)
  ·
    refine ⟨11671198701445283516840455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 248985572297499381692596373 11671198701445283516840455)
    ·
      refine ⟨17506798052167925275260683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11671198701445283516840455 17506798052167925275260683)
      ·
        refine ⟨26260197078251887912891025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17506798052167925275260683 26260197078251887912891025)
        ·
          refine ⟨19695147808688915934668269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26260197078251887912891025 19695147808688915934668269)
          ·
            refine ⟨7385680428258343475500601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19695147808688915934668269 7385680428258343475500601)
            ·
              refine ⟨5539260321193757606625451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7385680428258343475500601 5539260321193757606625451)
              ·
                refine ⟨8308890481790636409938177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5539260321193757606625451 8308890481790636409938177)
                ·
                  refine ⟨6231667861342977307453633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8308890481790636409938177 6231667861342977307453633)
                  ·
                    refine ⟨4673750896007232980590225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6231667861342977307453633 4673750896007232980590225)
                    ·
                      refine ⟨3505313172005424735442669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4673750896007232980590225 3505313172005424735442669)
                      ·
                        rfl

theorem cell23_6826573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_6826573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826573 prefixEnd_6826573 := by exact prefixLift 6826573
  have htrace : WordTrace (prefixWord ++ tailWord_6826573) baseStart_6826573 baseEnd_6826573 := by
    simpa [prefixWord, tailWord_6826573, baseEnd_6826573] using wordTrace_append hprefix tailTrace_6826573
  have hstable : (prefixWord ++ tailWord_6826573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826573).length < 2 ^ (prefixWord ++ tailWord_6826573).sum := by decide
  have hdescent : baseEnd_6826573 < baseStart_6826573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826595 : List Nat := [1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 4]
def baseStart_6826595 : Nat := 118140960795 + 6826595 * 2 ^ 59
def prefixEnd_6826595 : Nat := 4983230072969 + 3 ^ 40 * 6826595 * 2
def baseEnd_6826595 : Nat := 3505324468579823649367567

theorem tailTrace_6826595 : CollatzResearch.WordTrace tailWord_6826595 prefixEnd_6826595 3505324468579823649367567 := by
  unfold tailWord_6826595
  simp only [CollatzResearch.WordTrace]
  refine ⟨248986374703419679449897239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165990916468946452966598159 248986374703419679449897239)
  ·
    refine ⟨373479562055129519174845859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248986374703419679449897239 373479562055129519174845859)
    ·
      refine ⟨560219343082694278762268789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373479562055129519174845859 560219343082694278762268789)
      ·
        refine ⟨52520563414002588633962699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 560219343082694278762268789 52520563414002588633962699)
        ·
          refine ⟨78780845121003882950944049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52520563414002588633962699 78780845121003882950944049)
          ·
            refine ⟨59085633840752912213208037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78780845121003882950944049 59085633840752912213208037)
            ·
              refine ⟨11078556345141171039976507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59085633840752912213208037 11078556345141171039976507)
              ·
                refine ⟨16617834517711756559964761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11078556345141171039976507 16617834517711756559964761)
                ·
                  refine ⟨12463375888283817419973571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16617834517711756559964761 12463375888283817419973571)
                  ·
                    refine ⟨18695063832425726129960357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12463375888283817419973571 18695063832425726129960357)
                    ·
                      refine ⟨3505324468579823649367567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18695063832425726129960357 3505324468579823649367567)
                      ·
                        rfl

theorem cell23_6826595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_6826595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826595 prefixEnd_6826595 := by exact prefixLift 6826595
  have htrace : WordTrace (prefixWord ++ tailWord_6826595) baseStart_6826595 baseEnd_6826595 := by
    simpa [prefixWord, tailWord_6826595, baseEnd_6826595] using wordTrace_append hprefix tailTrace_6826595
  have hstable : (prefixWord ++ tailWord_6826595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826595).length < 2 ^ (prefixWord ++ tailWord_6826595).sum := by decide
  have hdescent : baseEnd_6826595 < baseStart_6826595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826615 : List Nat := [1, 1, 3, 1, 1, 3, 4, 2, 2, 2, 3]
def baseStart_6826615 : Nat := 118140960795 + 6826615 * 2 ^ 59
def prefixEnd_6826615 : Nat := 4983230072969 + 3 ^ 40 * 6826615 * 2
def baseEnd_6826615 : Nat := 3505334738192913571117475

theorem tailTrace_6826615 : CollatzResearch.WordTrace tailWord_6826615 prefixEnd_6826615 3505334738192913571117475 := by
  unfold tailWord_6826615
  simp only [CollatzResearch.WordTrace]
  refine ⟨248987104163347222865625299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165991402775564815243750199 248987104163347222865625299)
  ·
    refine ⟨373480656245020834298437949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248987104163347222865625299 373480656245020834298437949)
    ·
      refine ⟨140055246091882812861914231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373480656245020834298437949 140055246091882812861914231)
      ·
        refine ⟨210082869137824219292871347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140055246091882812861914231 210082869137824219292871347)
        ·
          refine ⟨315124303706736328939307021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210082869137824219292871347 315124303706736328939307021)
          ·
            refine ⟨118171613890026123352240133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 315124303706736328939307021 118171613890026123352240133)
            ·
              refine ⟨22157177604379898128545025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118171613890026123352240133 22157177604379898128545025)
              ·
                refine ⟨16617883203284923596408769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22157177604379898128545025 16617883203284923596408769)
                ·
                  refine ⟨12463412402463692697306577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16617883203284923596408769 12463412402463692697306577)
                  ·
                    refine ⟨9347559301847769522979933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12463412402463692697306577 9347559301847769522979933)
                    ·
                      refine ⟨3505334738192913571117475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9347559301847769522979933 3505334738192913571117475)
                      ·
                        rfl

theorem cell23_6826615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 2, 3].length) (baseStart_6826615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826615 prefixEnd_6826615 := by exact prefixLift 6826615
  have htrace : WordTrace (prefixWord ++ tailWord_6826615) baseStart_6826615 baseEnd_6826615 := by
    simpa [prefixWord, tailWord_6826615, baseEnd_6826615] using wordTrace_append hprefix tailTrace_6826615
  have hstable : (prefixWord ++ tailWord_6826615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826615).length < 2 ^ (prefixWord ++ tailWord_6826615).sum := by decide
  have hdescent : baseEnd_6826615 < baseStart_6826615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826679 : List Nat := [1, 1, 3, 1, 6, 1, 2, 1, 3, 1, 3]
def baseStart_6826679 : Nat := 118140960795 + 6826679 * 2 ^ 59
def prefixEnd_6826679 : Nat := 4983230072969 + 3 ^ 40 * 6826679 * 2
def baseEnd_6826679 : Nat := 3505367600954801320717181

theorem tailTrace_6826679 : CollatzResearch.WordTrace tailWord_6826679 prefixEnd_6826679 3505367600954801320717181 := by
  unfold tailWord_6826679
  simp only [CollatzResearch.WordTrace]
  refine ⟨248989438435115361795955091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165992958956743574530636727 248989438435115361795955091)
  ·
    refine ⟨373484157652673042693932637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248989438435115361795955091 373484157652673042693932637)
    ·
      refine ⟨140056559119752391010224739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373484157652673042693932637 140056559119752391010224739)
      ·
        refine ⟨210084838679628586515337109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140056559119752391010224739 210084838679628586515337109)
        ·
          refine ⟨9847726813107589992906427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 210084838679628586515337109 9847726813107589992906427)
          ·
            refine ⟨14771590219661384989359641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9847726813107589992906427 14771590219661384989359641)
            ·
              refine ⟨11078692664746038742019731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14771590219661384989359641 11078692664746038742019731)
              ·
                refine ⟨16618038997119058113029597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11078692664746038742019731 16618038997119058113029597)
                ·
                  refine ⟨6231764623919646792386099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16618038997119058113029597 6231764623919646792386099)
                  ·
                    refine ⟨9347646935879470188579149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6231764623919646792386099 9347646935879470188579149)
                    ·
                      refine ⟨3505367600954801320717181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9347646935879470188579149 3505367600954801320717181)
                      ·
                        rfl

theorem cell23_6826679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 3, 1, 3].length) (baseStart_6826679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826679 prefixEnd_6826679 := by exact prefixLift 6826679
  have htrace : WordTrace (prefixWord ++ tailWord_6826679) baseStart_6826679 baseEnd_6826679 := by
    simpa [prefixWord, tailWord_6826679, baseEnd_6826679] using wordTrace_append hprefix tailTrace_6826679
  have hstable : (prefixWord ++ tailWord_6826679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826679).length < 2 ^ (prefixWord ++ tailWord_6826679).sum := by decide
  have hdescent : baseEnd_6826679 < baseStart_6826679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826702 : List Nat := [4, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4]
def baseStart_6826702 : Nat := 118140960795 + 6826702 * 2 ^ 59
def prefixEnd_6826702 : Nat := 4983230072969 + 3 ^ 40 * 6826702 * 2
def baseEnd_6826702 : Nat := 3505379411009854730729575

theorem tailTrace_6826702 : CollatzResearch.WordTrace tailWord_6826702 prefixEnd_6826702 3505379411009854730729575 := by
  unfold tailWord_6826702
  simp only [CollatzResearch.WordTrace]
  refine ⟨31123784664254004590505295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165993518209354691149361573 31123784664254004590505295)
  ·
    refine ⟨46685676996381006885757943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31123784664254004590505295 46685676996381006885757943)
    ·
      refine ⟨70028515494571510328636915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46685676996381006885757943 70028515494571510328636915)
      ·
        refine ⟨105042773241857265492955373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70028515494571510328636915 105042773241857265492955373)
        ·
          refine ⟨39391039965696474559858265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105042773241857265492955373 39391039965696474559858265)
          ·
            refine ⟨29543279974272355919893699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39391039965696474559858265 29543279974272355919893699)
            ·
              refine ⟨44314919961408533879840549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29543279974272355919893699 44314919961408533879840549)
              ·
                refine ⟨8309047492764100102470103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44314919961408533879840549 8309047492764100102470103)
                ·
                  refine ⟨12463571239146150153705155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8309047492764100102470103 12463571239146150153705155)
                  ·
                    refine ⟨18695356858719225230557733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12463571239146150153705155 18695356858719225230557733)
                    ·
                      refine ⟨3505379411009854730729575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18695356858719225230557733 3505379411009854730729575)
                      ·
                        rfl

theorem cell23_6826702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_6826702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826702 prefixEnd_6826702 := by exact prefixLift 6826702
  have htrace : WordTrace (prefixWord ++ tailWord_6826702) baseStart_6826702 baseEnd_6826702 := by
    simpa [prefixWord, tailWord_6826702, baseEnd_6826702] using wordTrace_append hprefix tailTrace_6826702
  have hstable : (prefixWord ++ tailWord_6826702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826702).length < 2 ^ (prefixWord ++ tailWord_6826702).sum := by decide
  have hdescent : baseEnd_6826702 < baseStart_6826702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826725 : List Nat := [1, 3, 1, 4, 1, 4, 9]
def baseStart_6826725 : Nat := 118140960795 + 6826725 * 2 ^ 59
def prefixEnd_6826725 : Nat := 4983230072969 + 3 ^ 40 * 6826725 * 2
def baseEnd_6826725 : Nat := 43276434827961828898049

theorem tailTrace_6826725 : CollatzResearch.WordTrace tailWord_6826725 prefixEnd_6826725 43276434827961828898049 := by
  unfold tailWord_6826725
  simp only [CollatzResearch.WordTrace]
  refine ⟨248991116192948711652129629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165994077461965807768086419 248991116192948711652129629)
  ·
    refine ⟨93371668572355766869548611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248991116192948711652129629 93371668572355766869548611)
    ·
      refine ⟨140057502858533650304322917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93371668572355766869548611 140057502858533650304322917)
      ·
        refine ⟨26260781785975059432060547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140057502858533650304322917 26260781785975059432060547)
        ·
          refine ⟨39391172678962589148090821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26260781785975059432060547 39391172678962589148090821)
          ·
            refine ⟨7385844877305485465267029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39391172678962589148090821 7385844877305485465267029)
            ·
              refine ⟨43276434827961828898049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7385844877305485465267029 43276434827961828898049)
              ·
                rfl

theorem cell23_6826725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 9].length) (baseStart_6826725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826725 prefixEnd_6826725 := by exact prefixLift 6826725
  have htrace : WordTrace (prefixWord ++ tailWord_6826725) baseStart_6826725 baseEnd_6826725 := by
    simpa [prefixWord, tailWord_6826725, baseEnd_6826725] using wordTrace_append hprefix tailTrace_6826725
  have hstable : (prefixWord ++ tailWord_6826725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826725).length < 2 ^ (prefixWord ++ tailWord_6826725).sum := by decide
  have hdescent : baseEnd_6826725 < baseStart_6826725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826785 : List Nat := [1, 2, 3, 2, 1, 2, 2, 2, 2, 6]
def baseStart_6826785 : Nat := 118140960795 + 6826785 * 2 ^ 59
def prefixEnd_6826785 : Nat := 4983230072969 + 3 ^ 40 * 6826785 * 2
def baseEnd_6826785 : Nat := 1168474009968059301997231

theorem tailTrace_6826785 : CollatzResearch.WordTrace tailWord_6826785 prefixEnd_6826785 1168474009968059301997231 := by
  unfold tailWord_6826785
  simp only [CollatzResearch.WordTrace]
  refine ⟨248993304572731341899313809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165995536381820894599542539 248993304572731341899313809)
  ·
    refine ⟨186744978429548506424485357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248993304572731341899313809 186744978429548506424485357)
    ·
      refine ⟨70029366911080689909182009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186744978429548506424485357 70029366911080689909182009)
      ·
        refine ⟨52522025183310517431886507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70029366911080689909182009 52522025183310517431886507)
        ·
          refine ⟨78783037774965776147829761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52522025183310517431886507 78783037774965776147829761)
          ·
            refine ⟨59087278331224332110872321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78783037774965776147829761 59087278331224332110872321)
            ·
              refine ⟨44315458748418249083154241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59087278331224332110872321 44315458748418249083154241)
              ·
                refine ⟨33236594061313686812365681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44315458748418249083154241 33236594061313686812365681)
                ·
                  refine ⟨24927445545985265109274261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33236594061313686812365681 24927445545985265109274261)
                  ·
                    refine ⟨1168474009968059301997231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24927445545985265109274261 1168474009968059301997231)
                    ·
                      rfl

theorem cell23_6826785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_6826785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826785 prefixEnd_6826785 := by exact prefixLift 6826785
  have htrace : WordTrace (prefixWord ++ tailWord_6826785) baseStart_6826785 baseEnd_6826785 := by
    simpa [prefixWord, tailWord_6826785, baseEnd_6826785] using wordTrace_append hprefix tailTrace_6826785
  have hstable : (prefixWord ++ tailWord_6826785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826785).length < 2 ^ (prefixWord ++ tailWord_6826785).sum := by decide
  have hdescent : baseEnd_6826785 < baseStart_6826785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826786 : List Nat := [3, 3, 1, 1, 2, 3, 2, 2, 2, 1, 3]
def baseStart_6826786 : Nat := 118140960795 + 6826786 * 2 ^ 59
def prefixEnd_6826786 : Nat := 4983230072969 + 3 ^ 40 * 6826786 * 2
def baseEnd_6826786 : Nat := 3505422543384832402079189

theorem tailTrace_6826786 : CollatzResearch.WordTrace tailWord_6826786 prefixEnd_6826786 3505422543384832402079189 := by
  unfold tailWord_6826786
  simp only [CollatzResearch.WordTrace]
  refine ⟨62248335261431929767525053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165995560697151812713400141 62248335261431929767525053)
  ·
    refine ⟨23343125723036973662821895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62248335261431929767525053 23343125723036973662821895)
    ·
      refine ⟨35014688584555460494232843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23343125723036973662821895 35014688584555460494232843)
      ·
        refine ⟨52522032876833190741349265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35014688584555460494232843 52522032876833190741349265)
        ·
          refine ⟨39391524657624893056011949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52522032876833190741349265 39391524657624893056011949)
          ·
            refine ⟨14771821746609334896004481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39391524657624893056011949 14771821746609334896004481)
            ·
              refine ⟨11078866309957001172003361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14771821746609334896004481 11078866309957001172003361)
              ·
                refine ⟨8309149732467750879002521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11078866309957001172003361 8309149732467750879002521)
                ·
                  refine ⟨6231862299350813159251891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8309149732467750879002521 6231862299350813159251891)
                  ·
                    refine ⟨9347793449026219738877837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6231862299350813159251891 9347793449026219738877837)
                    ·
                      refine ⟨3505422543384832402079189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9347793449026219738877837 3505422543384832402079189)
                      ·
                        rfl

theorem cell23_6826786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_6826786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826786 prefixEnd_6826786 := by exact prefixLift 6826786
  have htrace : WordTrace (prefixWord ++ tailWord_6826786) baseStart_6826786 baseEnd_6826786 := by
    simpa [prefixWord, tailWord_6826786, baseEnd_6826786] using wordTrace_append hprefix tailTrace_6826786
  have hstable : (prefixWord ++ tailWord_6826786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826786).length < 2 ^ (prefixWord ++ tailWord_6826786).sum := by decide
  have hdescent : baseEnd_6826786 < baseStart_6826786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826795 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 2, 4, 3]
def baseStart_6826795 : Nat := 118140960795 + 6826795 * 2 ^ 59
def prefixEnd_6826795 : Nat := 4983230072969 + 3 ^ 40 * 6826795 * 2
def baseEnd_6826795 : Nat := 3505427164710722866866647

theorem tailTrace_6826795 : CollatzResearch.WordTrace tailWord_6826795 prefixEnd_6826795 3505427164710722866866647 := by
  unfold tailWord_6826795
  simp only [CollatzResearch.WordTrace]
  refine ⟨248993669302695113607177839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165995779535130075738118559 248993669302695113607177839)
  ·
    refine ⟨373490503954042670410766759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248993669302695113607177839 373490503954042670410766759)
    ·
      refine ⟨560235755931064005616150139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373490503954042670410766759 560235755931064005616150139)
      ·
        refine ⟨840353633896596008424225209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560235755931064005616150139 840353633896596008424225209)
        ·
          refine ⟨630265225422447006318168907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 840353633896596008424225209 630265225422447006318168907)
          ·
            refine ⟨945397838133670509477253361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630265225422447006318168907 945397838133670509477253361)
            ·
              refine ⟨709048378600252882107940021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 945397838133670509477253361 709048378600252882107940021)
              ·
                refine ⟨66473285493773707697619377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 709048378600252882107940021 66473285493773707697619377)
                ·
                  refine ⟨49854964120330280773214533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66473285493773707697619377 49854964120330280773214533)
                  ·
                    refine ⟨9347805772561927644977725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49854964120330280773214533 9347805772561927644977725)
                    ·
                      refine ⟨3505427164710722866866647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9347805772561927644977725 3505427164710722866866647)
                      ·
                        rfl

theorem cell23_6826795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 4, 3].length) (baseStart_6826795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826795 prefixEnd_6826795 := by exact prefixLift 6826795
  have htrace : WordTrace (prefixWord ++ tailWord_6826795) baseStart_6826795 baseEnd_6826795 := by
    simpa [prefixWord, tailWord_6826795, baseEnd_6826795] using wordTrace_append hprefix tailTrace_6826795
  have hstable : (prefixWord ++ tailWord_6826795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826795).length < 2 ^ (prefixWord ++ tailWord_6826795).sum := by decide
  have hdescent : baseEnd_6826795 < baseStart_6826795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826815 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 9]
def baseStart_6826815 : Nat := 118140960795 + 6826815 * 2 ^ 59
def prefixEnd_6826815 : Nat := 4983230072969 + 3 ^ 40 * 6826815 * 2
def baseEnd_6826815 : Nat := 389493048258201420957395

theorem tailTrace_6826815 : CollatzResearch.WordTrace tailWord_6826815 prefixEnd_6826815 389493048258201420957395 := by
  unfold tailWord_6826815
  simp only [CollatzResearch.WordTrace]
  refine ⟨248994398762622657022905899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165996265841748438015270599 248994398762622657022905899)
  ·
    refine ⟨373491598143933985534358849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248994398762622657022905899 373491598143933985534358849)
    ·
      refine ⟨280118698607950489150769137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373491598143933985534358849 280118698607950489150769137)
      ·
        refine ⟨210089023955962866863076853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280118698607950489150769137 210089023955962866863076853)
        ·
          refine ⟨19695845995871518768413455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 210089023955962866863076853 19695845995871518768413455)
          ·
            refine ⟨29543768993807278152620183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19695845995871518768413455 29543768993807278152620183)
            ·
              refine ⟨44315653490710917228930275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29543768993807278152620183 44315653490710917228930275)
              ·
                refine ⟨66473480236066375843395413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44315653490710917228930275 66473480236066375843395413)
                ·
                  refine ⟨389493048258201420957395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66473480236066375843395413 389493048258201420957395)
                  ·
                    rfl

theorem cell23_6826815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 9].length) (baseStart_6826815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826815 prefixEnd_6826815 := by exact prefixLift 6826815
  have htrace : WordTrace (prefixWord ++ tailWord_6826815) baseStart_6826815 baseEnd_6826815 := by
    simpa [prefixWord, tailWord_6826815, baseEnd_6826815] using wordTrace_append hprefix tailTrace_6826815
  have hstable : (prefixWord ++ tailWord_6826815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826815).length < 2 ^ (prefixWord ++ tailWord_6826815).sum := by decide
  have hdescent : baseEnd_6826815 < baseStart_6826815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826832 : List Nat := [2, 1, 1, 1, 1, 4, 3, 5, 5]
def baseStart_6826832 : Nat := 118140960795 + 6826832 * 2 ^ 59
def prefixEnd_6826832 : Nat := 4983230072969 + 3 ^ 40 * 6826832 * 2
def baseEnd_6826832 : Nat := 389494018166104358011553

theorem tailTrace_6826832 : CollatzResearch.WordTrace tailWord_6826832 prefixEnd_6826832 389494018166104358011553 := by
  unfold tailWord_6826832
  simp only [CollatzResearch.WordTrace]
  refine ⟨124497509401780534463137375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165996679202374045950849833 124497509401780534463137375)
  ·
    refine ⟨186746264102670801694706063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124497509401780534463137375 186746264102670801694706063)
    ·
      refine ⟨280119396154006202542059095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186746264102670801694706063 280119396154006202542059095)
      ·
        refine ⟨420179094231009303813088643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280119396154006202542059095 420179094231009303813088643)
        ·
          refine ⟨630268641346513955719632965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420179094231009303813088643 630268641346513955719632965)
          ·
            refine ⟨118175370252471366697431181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 630268641346513955719632965 118175370252471366697431181)
            ·
              refine ⟨44315763844676762511536693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118175370252471366697431181 44315763844676762511536693)
              ·
                refine ⟨4154602860438446485456565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44315763844676762511536693 4154602860438446485456565)
                ·
                  refine ⟨389494018166104358011553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4154602860438446485456565 389494018166104358011553)
                  ·
                    rfl

theorem cell23_6826832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 5, 5].length) (baseStart_6826832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826832 prefixEnd_6826832 := by exact prefixLift 6826832
  have htrace : WordTrace (prefixWord ++ tailWord_6826832) baseStart_6826832 baseEnd_6826832 := by
    simpa [prefixWord, tailWord_6826832, baseEnd_6826832] using wordTrace_append hprefix tailTrace_6826832
  have hstable : (prefixWord ++ tailWord_6826832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826832).length < 2 ^ (prefixWord ++ tailWord_6826832).sum := by decide
  have hdescent : baseEnd_6826832 < baseStart_6826832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826842 : List Nat := [3, 1, 1, 2, 1, 4, 1, 2, 2, 3, 3]
def baseStart_6826842 : Nat := 118140960795 + 6826842 * 2 ^ 59
def prefixEnd_6826842 : Nat := 4983230072969 + 3 ^ 40 * 6826842 * 2
def baseEnd_6826842 : Nat := 3505451298301484182978931

theorem tailTrace_6826842 : CollatzResearch.WordTrace tailWord_6826842 prefixEnd_6826842 3505451298301484182978931 := by
  unfold tailWord_6826842
  simp only [CollatzResearch.WordTrace]
  refine ⟨62248845883381210158534695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165996922355683227089425853 62248845883381210158534695)
  ·
    refine ⟨93373268825071815237802043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62248845883381210158534695 93373268825071815237802043)
    ·
      refine ⟨140059903237607722856703065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93373268825071815237802043 140059903237607722856703065)
      ·
        refine ⟨105044927428205792142527299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140059903237607722856703065 105044927428205792142527299)
        ·
          refine ⟨157567391142308688213790949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105044927428205792142527299 157567391142308688213790949)
          ·
            refine ⟨29543885839182879040085803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157567391142308688213790949 29543885839182879040085803)
            ·
              refine ⟨44315828758774318560128705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29543885839182879040085803 44315828758774318560128705)
              ·
                refine ⟨33236871569080738920096529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44315828758774318560128705 33236871569080738920096529)
                ·
                  refine ⟨24927653676810554190072397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33236871569080738920096529 24927653676810554190072397)
                  ·
                    refine ⟨9347870128803957821277149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24927653676810554190072397 9347870128803957821277149)
                    ·
                      refine ⟨3505451298301484182978931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9347870128803957821277149 3505451298301484182978931)
                      ·
                        rfl

theorem cell23_6826842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_6826842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826842 prefixEnd_6826842 := by exact prefixLift 6826842
  have htrace : WordTrace (prefixWord ++ tailWord_6826842) baseStart_6826842 baseEnd_6826842 := by
    simpa [prefixWord, tailWord_6826842, baseEnd_6826842] using wordTrace_append hprefix tailTrace_6826842
  have hstable : (prefixWord ++ tailWord_6826842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826842).length < 2 ^ (prefixWord ++ tailWord_6826842).sum := by decide
  have hdescent : baseEnd_6826842 < baseStart_6826842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826892 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 5, 4]
def baseStart_6826892 : Nat := 118140960795 + 6826892 * 2 ^ 59
def prefixEnd_6826892 : Nat := 4983230072969 + 3 ^ 40 * 6826892 * 2
def baseEnd_6826892 : Nat := 1168492324111402995784567

theorem tailTrace_6826892 : CollatzResearch.WordTrace tailWord_6826892 prefixEnd_6826892 1168492324111402995784567 := by
  unfold tailWord_6826892
  simp only [CollatzResearch.WordTrace]
  refine ⟨124498603591671849586729465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165998138122229132782305953 124498603591671849586729465)
  ·
    refine ⟨93373952693753887190047099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124498603591671849586729465 93373952693753887190047099)
    ·
      refine ⟨140060929040630830785070649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93373952693753887190047099 140060929040630830785070649)
      ·
        refine ⟨105045696780473123088802987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140060929040630830785070649 105045696780473123088802987)
        ·
          refine ⟨157568545170709684633204481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105045696780473123088802987 157568545170709684633204481)
          ·
            refine ⟨118176408878032263474903361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157568545170709684633204481 118176408878032263474903361)
            ·
              refine ⟨88632306658524197606177521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118176408878032263474903361 88632306658524197606177521)
              ·
                refine ⟨66474229993893148204633141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88632306658524197606177521 66474229993893148204633141)
                ·
                  refine ⟨6231959061927482644184357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66474229993893148204633141 6231959061927482644184357)
                  ·
                    refine ⟨1168492324111402995784567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6231959061927482644184357 1168492324111402995784567)
                    ·
                      rfl

theorem cell23_6826892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 5, 4].length) (baseStart_6826892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826892 prefixEnd_6826892 := by exact prefixLift 6826892
  have htrace : WordTrace (prefixWord ++ tailWord_6826892) baseStart_6826892 baseEnd_6826892 := by
    simpa [prefixWord, tailWord_6826892, baseEnd_6826892] using wordTrace_append hprefix tailTrace_6826892
  have hstable : (prefixWord ++ tailWord_6826892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826892).length < 2 ^ (prefixWord ++ tailWord_6826892).sum := by decide
  have hdescent : baseEnd_6826892 < baseStart_6826892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6826993 : List Nat := [1, 2, 2, 2, 4, 3, 1, 1, 2, 3, 2]
def baseStart_6826993 : Nat := 118140960795 + 6826993 * 2 ^ 59
def prefixEnd_6826993 : Nat := 4983230072969 + 3 ^ 40 * 6826993 * 2
def baseEnd_6826993 : Nat := 3505528833880313092190737

theorem tailTrace_6826993 : CollatzResearch.WordTrace tailWord_6826993 prefixEnd_6826993 3505528833880313092190737 := by
  unfold tailWord_6826993
  simp only [CollatzResearch.WordTrace]
  refine ⟨249000890955977793422885633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166000593970651862281923755 249000890955977793422885633)
  ·
    refine ⟨186750668216983345067164225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249000890955977793422885633 186750668216983345067164225)
    ·
      refine ⟨140063001162737508800373169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186750668216983345067164225 140063001162737508800373169)
      ·
        refine ⟨105047250872053131600279877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140063001162737508800373169 105047250872053131600279877)
        ·
          refine ⟨19696359538509962175052477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105047250872053131600279877 19696359538509962175052477)
          ·
            refine ⟨7386134826941235815644679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19696359538509962175052477 7386134826941235815644679)
            ·
              refine ⟨11079202240411853723467019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7386134826941235815644679 11079202240411853723467019)
              ·
                refine ⟨16618803360617780585200529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11079202240411853723467019 16618803360617780585200529)
                ·
                  refine ⟨12464102520463335438900397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16618803360617780585200529 12464102520463335438900397)
                  ·
                    refine ⟨4674038445173750789587649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12464102520463335438900397 4674038445173750789587649)
                    ·
                      refine ⟨3505528833880313092190737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4674038445173750789587649 3505528833880313092190737)
                      ·
                        rfl

theorem cell23_6826993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 3, 2].length) (baseStart_6826993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6826993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6826993 prefixEnd_6826993 := by exact prefixLift 6826993
  have htrace : WordTrace (prefixWord ++ tailWord_6826993) baseStart_6826993 baseEnd_6826993 := by
    simpa [prefixWord, tailWord_6826993, baseEnd_6826993] using wordTrace_append hprefix tailTrace_6826993
  have hstable : (prefixWord ++ tailWord_6826993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6826993).length < 2 ^ (prefixWord ++ tailWord_6826993).sum := by decide
  have hdescent : baseEnd_6826993 < baseStart_6826993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6826993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827016 : List Nat := [2, 1, 3, 2, 1, 3, 3, 2, 2, 4]
def baseStart_6827016 : Nat := 118140960795 + 6827016 * 2 ^ 59
def prefixEnd_6827016 : Nat := 4983230072969 + 3 ^ 40 * 6827016 * 2
def baseEnd_6827016 : Nat := 1168513547978455500734377

theorem tailTrace_6827016 : CollatzResearch.WordTrace tailWord_6827016 prefixEnd_6827016 1168513547978455500734377 := by
  unfold tailWord_6827016
  simp only [CollatzResearch.WordTrace]
  refine ⟨124500864917447234175486451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166001153223262978900648601 124500864917447234175486451)
  ·
    refine ⟨186751297376170851263229677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124500864917447234175486451 186751297376170851263229677)
    ·
      refine ⟨70031736516064069223711129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186751297376170851263229677 70031736516064069223711129)
      ·
        refine ⟨52523802387048051917783347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70031736516064069223711129 52523802387048051917783347)
        ·
          refine ⟨78785703580572077876675021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52523802387048051917783347 78785703580572077876675021)
          ·
            refine ⟨29544638842714529203753133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78785703580572077876675021 29544638842714529203753133)
            ·
              refine ⟨11079239566017948451407425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29544638842714529203753133 11079239566017948451407425)
              ·
                refine ⟨8309429674513461338555569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11079239566017948451407425 8309429674513461338555569)
                ·
                  refine ⟨6232072255885096003916677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8309429674513461338555569 6232072255885096003916677)
                  ·
                    refine ⟨1168513547978455500734377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6232072255885096003916677 1168513547978455500734377)
                    ·
                      rfl

theorem cell23_6827016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_6827016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827016 prefixEnd_6827016 := by exact prefixLift 6827016
  have htrace : WordTrace (prefixWord ++ tailWord_6827016) baseStart_6827016 baseEnd_6827016 := by
    simpa [prefixWord, tailWord_6827016, baseEnd_6827016] using wordTrace_append hprefix tailTrace_6827016
  have hstable : (prefixWord ++ tailWord_6827016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827016).length < 2 ^ (prefixWord ++ tailWord_6827016).sum := by decide
  have hdescent : baseEnd_6827016 < baseStart_6827016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827052 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 5]
def baseStart_6827052 : Nat := 118140960795 + 6827052 * 2 ^ 59
def prefixEnd_6827052 : Nat := 4983230072969 + 3 ^ 40 * 6827052 * 2
def baseEnd_6827052 : Nat := 3505559129238928361352965

theorem tailTrace_6827052 : CollatzResearch.WordTrace tailWord_6827052 prefixEnd_6827052 3505559129238928361352965 := by
  unfold tailWord_6827052
  simp only [CollatzResearch.WordTrace]
  refine ⟨124501521431382023249641705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166002028575176030999522273 124501521431382023249641705)
  ·
    refine ⟨93376141073536517437231279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124501521431382023249641705 93376141073536517437231279)
    ·
      refine ⟨140064211610304776155846919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93376141073536517437231279 140064211610304776155846919)
      ·
        refine ⟨210096317415457164233770379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140064211610304776155846919 210096317415457164233770379)
        ·
          refine ⟨315144476123185746350655569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210096317415457164233770379 315144476123185746350655569)
          ·
            refine ⟨236358357092389309762991677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315144476123185746350655569 236358357092389309762991677)
            ·
              refine ⟨88634383909645991161121879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236358357092389309762991677 88634383909645991161121879)
              ·
                refine ⟨132951575864468986741682819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88634383909645991161121879 132951575864468986741682819)
                ·
                  refine ⟨199427363796703480112524229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132951575864468986741682819 199427363796703480112524229)
                  ·
                    refine ⟨37392630711881902521098293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 199427363796703480112524229 37392630711881902521098293)
                    ·
                      refine ⟨3505559129238928361352965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37392630711881902521098293 3505559129238928361352965)
                      ·
                        rfl

theorem cell23_6827052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_6827052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827052 prefixEnd_6827052 := by exact prefixLift 6827052
  have htrace : WordTrace (prefixWord ++ tailWord_6827052) baseStart_6827052 baseEnd_6827052 := by
    simpa [prefixWord, tailWord_6827052, baseEnd_6827052] using wordTrace_append hprefix tailTrace_6827052
  have hstable : (prefixWord ++ tailWord_6827052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827052).length < 2 ^ (prefixWord ++ tailWord_6827052).sum := by decide
  have hdescent : baseEnd_6827052 < baseStart_6827052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827090 : List Nat := [3, 2, 2, 1, 3, 1, 4, 1, 2, 1, 3]
def baseStart_6827090 : Nat := 118140960795 + 6827090 * 2 ^ 59
def prefixEnd_6827090 : Nat := 4983230072969 + 3 ^ 40 * 6827090 * 2
def baseEnd_6827090 : Nat := 3505578641503799212677791

theorem tailTrace_6827090 : CollatzResearch.WordTrace tailWord_6827090 prefixEnd_6827090 3505578641503799212677791 := by
  unfold tailWord_6827090
  simp only [CollatzResearch.WordTrace]
  refine ⟨62251107209156594747291681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166002952557750919326111149 62251107209156594747291681)
  ·
    refine ⟨46688330406867446060468761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62251107209156594747291681 46688330406867446060468761)
    ·
      refine ⟨35016247805150584545351571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46688330406867446060468761 35016247805150584545351571)
      ·
        refine ⟨52524371707725876818027357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35016247805150584545351571 52524371707725876818027357)
        ·
          refine ⟨19696639390397203806760259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52524371707725876818027357 19696639390397203806760259)
          ·
            refine ⟨29544959085595805710140389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19696639390397203806760259 29544959085595805710140389)
            ·
              refine ⟨5539679828549213570651323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29544959085595805710140389 5539679828549213570651323)
              ·
                refine ⟨8309519742823820355976985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5539679828549213570651323 8309519742823820355976985)
                ·
                  refine ⟨6232139807117865266982739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8309519742823820355976985 6232139807117865266982739)
                  ·
                    refine ⟨9348209710676797900474109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6232139807117865266982739 9348209710676797900474109)
                    ·
                      refine ⟨3505578641503799212677791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9348209710676797900474109 3505578641503799212677791)
                      ·
                        rfl

theorem cell23_6827090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_6827090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827090 prefixEnd_6827090 := by exact prefixLift 6827090
  have htrace : WordTrace (prefixWord ++ tailWord_6827090) baseStart_6827090 baseEnd_6827090 := by
    simpa [prefixWord, tailWord_6827090, baseEnd_6827090] using wordTrace_append hprefix tailTrace_6827090
  have hstable : (prefixWord ++ tailWord_6827090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827090).length < 2 ^ (prefixWord ++ tailWord_6827090).sum := by decide
  have hdescent : baseEnd_6827090 < baseStart_6827090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827094 : List Nat := [5, 2, 2, 1, 3, 1, 1, 2, 1, 2, 3]
def baseStart_6827094 : Nat := 118140960795 + 6827094 * 2 ^ 59
def prefixEnd_6827094 : Nat := 4983230072969 + 3 ^ 40 * 6827094 * 2
def baseEnd_6827094 : Nat := 3505580695426417197027773

theorem tailTrace_6827094 : CollatzResearch.WordTrace tailWord_6827094 prefixEnd_6827094 3505580695426417197027773 := by
  unfold tailWord_6827094
  simp only [CollatzResearch.WordTrace]
  refine ⟨15562785920538242979519521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166003049819074591781541557 15562785920538242979519521)
  ·
    refine ⟨11672089440403682234639641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15562785920538242979519521 11672089440403682234639641)
    ·
      refine ⟨8754067080302761675979731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11672089440403682234639641 8754067080302761675979731)
      ·
        refine ⟨13131100620454142513969597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8754067080302761675979731 13131100620454142513969597)
        ·
          refine ⟨4924162732670303442738599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13131100620454142513969597 4924162732670303442738599)
          ·
            refine ⟨7386244099005455164107899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4924162732670303442738599 7386244099005455164107899)
            ·
              refine ⟨11079366148508182746161849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7386244099005455164107899 11079366148508182746161849)
              ·
                refine ⟨8309524611381137059621387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11079366148508182746161849 8309524611381137059621387)
                ·
                  refine ⟨12464286917071705589432081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8309524611381137059621387 12464286917071705589432081)
                  ·
                    refine ⟨9348215187803779192074061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12464286917071705589432081 9348215187803779192074061)
                    ·
                      refine ⟨3505580695426417197027773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9348215187803779192074061 3505580695426417197027773)
                      ·
                        rfl

theorem cell23_6827094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_6827094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827094 prefixEnd_6827094 := by exact prefixLift 6827094
  have htrace : WordTrace (prefixWord ++ tailWord_6827094) baseStart_6827094 baseEnd_6827094 := by
    simpa [prefixWord, tailWord_6827094, baseEnd_6827094] using wordTrace_append hprefix tailTrace_6827094
  have hstable : (prefixWord ++ tailWord_6827094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827094).length < 2 ^ (prefixWord ++ tailWord_6827094).sum := by decide
  have hdescent : baseEnd_6827094 < baseStart_6827094 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827096 : List Nat := [2, 1, 2, 2, 1, 3, 2, 3, 1, 4, 2]
def baseStart_6827096 : Nat := 118140960795 + 6827096 * 2 ^ 59
def prefixEnd_6827096 : Nat := 4983230072969 + 3 ^ 40 * 6827096 * 2
def baseEnd_6827096 : Nat := 3505581722387726189202763

theorem tailTrace_6827096 : CollatzResearch.WordTrace tailWord_6827096 prefixEnd_6827096 3505581722387726189202763 := by
  unfold tailWord_6827096
  simp only [CollatzResearch.WordTrace]
  refine ⟨124502323837302321006942571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166003098449736428009256761 124502323837302321006942571)
  ·
    refine ⟨186753485755953481510413857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124502323837302321006942571 186753485755953481510413857)
    ·
      refine ⟨140065114316965111132810393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186753485755953481510413857 140065114316965111132810393)
      ·
        refine ⟨105048835737723833349607795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140065114316965111132810393 105048835737723833349607795)
        ·
          refine ⟨157573253606585750024411693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105048835737723833349607795 157573253606585750024411693)
          ·
            refine ⟨59089970102469656259154385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157573253606585750024411693 59089970102469656259154385)
            ·
              refine ⟨44317477576852242194365789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59089970102469656259154385 44317477576852242194365789)
              ·
                refine ⟨16619054091319590822887171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44317477576852242194365789 16619054091319590822887171)
                ·
                  refine ⟨24928581136979386234330757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16619054091319590822887171 24928581136979386234330757)
                  ·
                    refine ⟨4674108963183634918937017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24928581136979386234330757 4674108963183634918937017)
                    ·
                      refine ⟨3505581722387726189202763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4674108963183634918937017 3505581722387726189202763)
                      ·
                        rfl

theorem cell23_6827096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 1, 4, 2].length) (baseStart_6827096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827096 prefixEnd_6827096 := by exact prefixLift 6827096
  have htrace : WordTrace (prefixWord ++ tailWord_6827096) baseStart_6827096 baseEnd_6827096 := by
    simpa [prefixWord, tailWord_6827096, baseEnd_6827096] using wordTrace_append hprefix tailTrace_6827096
  have hstable : (prefixWord ++ tailWord_6827096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827096).length < 2 ^ (prefixWord ++ tailWord_6827096).sum := by decide
  have hdescent : baseEnd_6827096 < baseStart_6827096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827126 : List Nat := [5, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4]
def baseStart_6827126 : Nat := 118140960795 + 6827126 * 2 ^ 59
def prefixEnd_6827126 : Nat := 4983230072969 + 3 ^ 40 * 6827126 * 2
def baseEnd_6827126 : Nat := 3505597126807361071827625

theorem tailTrace_6827126 : CollatzResearch.WordTrace tailWord_6827126 prefixEnd_6827126 3505597126807361071827625 := by
  unfold tailWord_6827126
  simp only [CollatzResearch.WordTrace]
  refine ⟨15562858866530997321092327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166003827909663971424984821 15562858866530997321092327)
  ·
    refine ⟨23344288299796495981638491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15562858866530997321092327 23344288299796495981638491)
    ·
      refine ⟨35016432449694743972457737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23344288299796495981638491 35016432449694743972457737)
      ·
        refine ⟨26262324337271057979343303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35016432449694743972457737 26262324337271057979343303)
        ·
          refine ⟨39393486505906586969014955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26262324337271057979343303 39393486505906586969014955)
          ·
            refine ⟨59090229758859880453522433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39393486505906586969014955 59090229758859880453522433)
            ·
              refine ⟨44317672319144910340141825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59090229758859880453522433 44317672319144910340141825)
              ·
                refine ⟨33238254239358682755106369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44317672319144910340141825 33238254239358682755106369)
                ·
                  refine ⟨24928690679519012066329777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33238254239358682755106369 24928690679519012066329777)
                  ·
                    refine ⟨18696518009639259049747333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24928690679519012066329777 18696518009639259049747333)
                    ·
                      refine ⟨3505597126807361071827625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18696518009639259049747333 3505597126807361071827625)
                      ·
                        rfl

theorem cell23_6827126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_6827126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827126 prefixEnd_6827126 := by exact prefixLift 6827126
  have htrace : WordTrace (prefixWord ++ tailWord_6827126) baseStart_6827126 baseEnd_6827126 := by
    simpa [prefixWord, tailWord_6827126, baseEnd_6827126] using wordTrace_append hprefix tailTrace_6827126
  have hstable : (prefixWord ++ tailWord_6827126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827126).length < 2 ^ (prefixWord ++ tailWord_6827126).sum := by decide
  have hdescent : baseEnd_6827126 < baseStart_6827126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827146 : List Nat := [3, 1, 2, 3, 1, 1, 3, 1, 2, 3, 3]
def baseStart_6827146 : Nat := 118140960795 + 6827146 * 2 ^ 59
def prefixEnd_6827146 : Nat := 4983230072969 + 3 ^ 40 * 6827146 * 2
def baseEnd_6827146 : Nat := 3505607396420450993577533

theorem tailTrace_6827146 : CollatzResearch.WordTrace tailWord_6827146 prefixEnd_6827146 3505607396420450993577533 := by
  unfold tailWord_6827146
  simp only [CollatzResearch.WordTrace]
  refine ⟨62251617831105875138301323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166004314216282333702136861 62251617831105875138301323)
  ·
    refine ⟨93377426746658812707451985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62251617831105875138301323 93377426746658812707451985)
    ·
      refine ⟨70033070059994109530588989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93377426746658812707451985 70033070059994109530588989)
      ·
        refine ⟨26262401272497791073970871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70033070059994109530588989 26262401272497791073970871)
        ·
          refine ⟨39393601908746686610956307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26262401272497791073970871 39393601908746686610956307)
          ·
            refine ⟨59090402863120029916434461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39393601908746686610956307 59090402863120029916434461)
            ·
              refine ⟨22158901073670011218662923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59090402863120029916434461 22158901073670011218662923)
              ·
                refine ⟨33238351610505016827994385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22158901073670011218662923 33238351610505016827994385)
                ·
                  refine ⟨24928763707878762620995789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33238351610505016827994385 24928763707878762620995789)
                  ·
                    refine ⟨9348286390454535982873421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24928763707878762620995789 9348286390454535982873421)
                    ·
                      refine ⟨3505607396420450993577533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9348286390454535982873421 3505607396420450993577533)
                      ·
                        rfl

theorem cell23_6827146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_6827146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827146 prefixEnd_6827146 := by exact prefixLift 6827146
  have htrace : WordTrace (prefixWord ++ tailWord_6827146) baseStart_6827146 baseEnd_6827146 := by
    simpa [prefixWord, tailWord_6827146, baseEnd_6827146] using wordTrace_append hprefix tailTrace_6827146
  have hstable : (prefixWord ++ tailWord_6827146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827146).length < 2 ^ (prefixWord ++ tailWord_6827146).sum := by decide
  have hdescent : baseEnd_6827146 < baseStart_6827146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827170 : List Nat := [3, 3, 1, 3, 2, 1, 2, 3, 5]
def baseStart_6827170 : Nat := 118140960795 + 6827170 * 2 ^ 59
def prefixEnd_6827170 : Nat := 4983230072969 + 3 ^ 40 * 6827170 * 2
def baseEnd_6827170 : Nat := 389513302217350988853047

theorem tailTrace_6827170 : CollatzResearch.WordTrace tailWord_6827170 prefixEnd_6827170 389513302217350988853047 := by
  unfold tailWord_6827170
  simp only [CollatzResearch.WordTrace]
  refine ⟨62251836669084138163019741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166004897784224368434719309 62251836669084138163019741)
  ·
    refine ⟨23344438750906551811132403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62251836669084138163019741 23344438750906551811132403)
    ·
      refine ⟨35016658126359827716698605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23344438750906551811132403 35016658126359827716698605)
      ·
        refine ⟨13131246797384935393761977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35016658126359827716698605 13131246797384935393761977)
        ·
          refine ⟨9848435098038701545321483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13131246797384935393761977 9848435098038701545321483)
          ·
            refine ⟨14772652647058052317982225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9848435098038701545321483 14772652647058052317982225)
            ·
              refine ⟨11079489485293539238486669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14772652647058052317982225 11079489485293539238486669)
              ·
                refine ⟨4154808556985077214432501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11079489485293539238486669 4154808556985077214432501)
                ·
                  refine ⟨389513302217350988853047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4154808556985077214432501 389513302217350988853047)
                  ·
                    rfl

theorem cell23_6827170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_6827170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827170 prefixEnd_6827170 := by exact prefixLift 6827170
  have htrace : WordTrace (prefixWord ++ tailWord_6827170) baseStart_6827170 baseEnd_6827170 := by
    simpa [prefixWord, tailWord_6827170, baseEnd_6827170] using wordTrace_append hprefix tailTrace_6827170
  have hstable : (prefixWord ++ tailWord_6827170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827170).length < 2 ^ (prefixWord ++ tailWord_6827170).sum := by decide
  have hdescent : baseEnd_6827170 < baseStart_6827170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827247 : List Nat := [1, 1, 2, 1, 7, 1, 3, 2, 1, 4]
def baseStart_6827247 : Nat := 118140960795 + 6827247 * 2 ^ 59
def prefixEnd_6827247 : Nat := 4983230072969 + 3 ^ 40 * 6827247 * 2
def baseEnd_6827247 : Nat := 1168553085988851699471523

theorem tailTrace_6827247 : CollatzResearch.WordTrace tailWord_6827247 prefixEnd_6827247 1168553085988851699471523 := by
  unfold tailWord_6827247
  simp only [CollatzResearch.WordTrace]
  refine ⟨249010155097057594802631995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166006770064705063201754663 249010155097057594802631995)
  ·
    refine ⟨373515232645586392203947993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249010155097057594802631995 373515232645586392203947993)
    ·
      refine ⟨280136424484189794152960995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373515232645586392203947993 280136424484189794152960995)
      ·
        refine ⟨420204636726284691229441493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280136424484189794152960995 420204636726284691229441493)
        ·
          refine ⟨9848546173272297450690035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 420204636726284691229441493 9848546173272297450690035)
          ·
            refine ⟨14772819259908446176035053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9848546173272297450690035 14772819259908446176035053)
            ·
              refine ⟨5539807222465667316013145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14772819259908446176035053 5539807222465667316013145)
              ·
                refine ⟨4154855416849250487009859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5539807222465667316013145 4154855416849250487009859)
                ·
                  refine ⟨6232283125273875730514789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4154855416849250487009859 6232283125273875730514789)
                  ·
                    refine ⟨1168553085988851699471523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6232283125273875730514789 1168553085988851699471523)
                    ·
                      rfl

theorem cell23_6827247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 2, 1, 4].length) (baseStart_6827247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827247 prefixEnd_6827247 := by exact prefixLift 6827247
  have htrace : WordTrace (prefixWord ++ tailWord_6827247) baseStart_6827247 baseEnd_6827247 := by
    simpa [prefixWord, tailWord_6827247, baseEnd_6827247] using wordTrace_append hprefix tailTrace_6827247
  have hstable : (prefixWord ++ tailWord_6827247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827247).length < 2 ^ (prefixWord ++ tailWord_6827247).sum := by decide
  have hdescent : baseEnd_6827247 < baseStart_6827247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827249 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 2, 1, 7]
def baseStart_6827249 : Nat := 118140960795 + 6827249 * 2 ^ 59
def prefixEnd_6827249 : Nat := 4983230072969 + 3 ^ 40 * 6827249 * 2
def baseEnd_6827249 : Nat := 3505660284927864090589559

theorem tailTrace_6827249 : CollatzResearch.WordTrace tailWord_6827249 prefixEnd_6827249 3505660284927864090589559 := by
  unfold tailWord_6827249
  simp only [CollatzResearch.WordTrace]
  refine ⟨249010228043050349144204801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166006818695366899429469867 249010228043050349144204801)
  ·
    refine ⟨186757671032287761858153601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249010228043050349144204801 186757671032287761858153601)
    ·
      refine ⟨140068253274215821393615201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186757671032287761858153601 140068253274215821393615201)
      ·
        refine ⟨105051189955661866045211401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140068253274215821393615201 105051189955661866045211401)
        ·
          refine ⟨78788392466746399533908551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105051189955661866045211401 78788392466746399533908551)
          ·
            refine ⟨118182588700119599300862827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78788392466746399533908551 118182588700119599300862827)
            ·
              refine ⟨177273883050179398951294241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118182588700119599300862827 177273883050179398951294241)
              ·
                refine ⟨132955412287634549213470681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177273883050179398951294241 132955412287634549213470681)
                ·
                  refine ⟨99716559215725911910103011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132955412287634549213470681 99716559215725911910103011)
                  ·
                    refine ⟨149574838823588867865154517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99716559215725911910103011 149574838823588867865154517)
                    ·
                      refine ⟨3505660284927864090589559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149574838823588867865154517 3505660284927864090589559)
                      ·
                        rfl

theorem cell23_6827249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_6827249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827249 prefixEnd_6827249 := by exact prefixLift 6827249
  have htrace : WordTrace (prefixWord ++ tailWord_6827249) baseStart_6827249 baseEnd_6827249 := by
    simpa [prefixWord, tailWord_6827249, baseEnd_6827249] using wordTrace_append hprefix tailTrace_6827249
  have hstable : (prefixWord ++ tailWord_6827249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827249).length < 2 ^ (prefixWord ++ tailWord_6827249).sum := by decide
  have hdescent : baseEnd_6827249 < baseStart_6827249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827260 : List Nat := [2, 2, 2, 1, 5, 2, 2, 1, 6]
def baseStart_6827260 : Nat := 118140960795 + 6827260 * 2 ^ 59
def prefixEnd_6827260 : Nat := 4983230072969 + 3 ^ 40 * 6827260 * 2
def baseEnd_6827260 : Nat := 389518437023895949728001

theorem tailTrace_6827260 : CollatzResearch.WordTrace tailWord_6827260 prefixEnd_6827260 389518437023895949728001 := by
  unfold tailWord_6827260
  simp only [CollatzResearch.WordTrace]
  refine ⟨124505314623005249011427617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166007086164006998681903489 124505314623005249011427617)
  ·
    refine ⟨93378985967253936758570713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124505314623005249011427617 93378985967253936758570713)
    ·
      refine ⟨70034239475440452568928035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93378985967253936758570713 70034239475440452568928035)
      ·
        refine ⟨105051359213160678853392053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70034239475440452568928035 105051359213160678853392053)
        ·
          refine ⟨9848564926233813642505505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105051359213160678853392053 9848564926233813642505505)
          ·
            refine ⟨7386423694675360231879129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9848564926233813642505505 7386423694675360231879129)
            ·
              refine ⟨5539817771006520173909347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7386423694675360231879129 5539817771006520173909347)
              ·
                refine ⟨8309726656509780260864021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5539817771006520173909347 8309726656509780260864021)
                ·
                  refine ⟨389518437023895949728001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8309726656509780260864021 389518437023895949728001)
                  ·
                    rfl

theorem cell23_6827260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 6].length) (baseStart_6827260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827260 prefixEnd_6827260 := by exact prefixLift 6827260
  have htrace : WordTrace (prefixWord ++ tailWord_6827260) baseStart_6827260 baseEnd_6827260 := by
    simpa [prefixWord, tailWord_6827260, baseEnd_6827260] using wordTrace_append hprefix tailTrace_6827260
  have hstable : (prefixWord ++ tailWord_6827260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827260).length < 2 ^ (prefixWord ++ tailWord_6827260).sum := by decide
  have hdescent : baseEnd_6827260 < baseStart_6827260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827279 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 5]
def baseStart_6827279 : Nat := 118140960795 + 6827279 * 2 ^ 59
def prefixEnd_6827279 : Nat := 4983230072969 + 3 ^ 40 * 6827279 * 2
def baseEnd_6827279 : Nat := 3505675689347498973214421

theorem tailTrace_6827279 : CollatzResearch.WordTrace tailWord_6827279 prefixEnd_6827279 3505675689347498973214421 := by
  unfold tailWord_6827279
  simp only [CollatzResearch.WordTrace]
  refine ⟨249011322232941664267796891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166007548155294442845197927 249011322232941664267796891)
  ·
    refine ⟨373516983349412496401695337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249011322232941664267796891 373516983349412496401695337)
    ·
      refine ⟨280137737512059372301271503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373516983349412496401695337 280137737512059372301271503)
      ·
        refine ⟨420206606268089058451907255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280137737512059372301271503 420206606268089058451907255)
        ·
          refine ⟨630309909402133587677860883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420206606268089058451907255 630309909402133587677860883)
          ·
            refine ⟨945464864103200381516791325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630309909402133587677860883 945464864103200381516791325)
            ·
              refine ⟨354549324038700143068796747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 945464864103200381516791325 354549324038700143068796747)
              ·
                refine ⟨531823986058050214603195121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354549324038700143068796747 531823986058050214603195121)
                ·
                  refine ⟨398867989543537660952396341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 531823986058050214603195121 398867989543537660952396341)
                  ·
                    refine ⟨37393874019706655714287157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 398867989543537660952396341 37393874019706655714287157)
                    ·
                      refine ⟨3505675689347498973214421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37393874019706655714287157 3505675689347498973214421)
                      ·
                        rfl

theorem cell23_6827279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 5].length) (baseStart_6827279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827279 prefixEnd_6827279 := by exact prefixLift 6827279
  have htrace : WordTrace (prefixWord ++ tailWord_6827279) baseStart_6827279 baseEnd_6827279 := by
    simpa [prefixWord, tailWord_6827279, baseEnd_6827279] using wordTrace_append hprefix tailTrace_6827279
  have hstable : (prefixWord ++ tailWord_6827279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827279).length < 2 ^ (prefixWord ++ tailWord_6827279).sum := by decide
  have hdescent : baseEnd_6827279 < baseStart_6827279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827289 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 2, 5, 6]
def baseStart_6827289 : Nat := 118140960795 + 6827289 * 2 ^ 59
def prefixEnd_6827289 : Nat := 4983230072969 + 3 ^ 40 * 6827289 * 2
def baseEnd_6827289 : Nat := 3505680824154043934089375

theorem tailTrace_6827289 : CollatzResearch.WordTrace tailWord_6827289 prefixEnd_6827289 3505680824154043934089375 := by
  unfold tailWord_6827289
  simp only [CollatzResearch.WordTrace]
  refine ⟨249011686962905435975660921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166007791308603623983773947 249011686962905435975660921)
  ·
    refine ⟨186758765222179076981745691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249011686962905435975660921 186758765222179076981745691)
    ·
      refine ⟨280138147833268615472618537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186758765222179076981745691 280138147833268615472618537)
      ·
        refine ⟨210103610874951461604463903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280138147833268615472618537 210103610874951461604463903)
        ·
          refine ⟨315155416312427192406695855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210103610874951461604463903 315155416312427192406695855)
          ·
            refine ⟨472733124468640788610043783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315155416312427192406695855 472733124468640788610043783)
            ·
              refine ⟨709099686702961182915065675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472733124468640788610043783 709099686702961182915065675)
              ·
                refine ⟨1063649530054441774372598513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 709099686702961182915065675 1063649530054441774372598513)
                ·
                  refine ⟨797737147540831330779448885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1063649530054441774372598513 797737147540831330779448885)
                  ·
                    refine ⟨74787857581952937260573333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 797737147540831330779448885 74787857581952937260573333)
                    ·
                      refine ⟨3505680824154043934089375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74787857581952937260573333 3505680824154043934089375)
                      ·
                        rfl

theorem cell23_6827289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_6827289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827289 prefixEnd_6827289 := by exact prefixLift 6827289
  have htrace : WordTrace (prefixWord ++ tailWord_6827289) baseStart_6827289 baseEnd_6827289 := by
    simpa [prefixWord, tailWord_6827289, baseEnd_6827289] using wordTrace_append hprefix tailTrace_6827289
  have hstable : (prefixWord ++ tailWord_6827289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827289).length < 2 ^ (prefixWord ++ tailWord_6827289).sum := by decide
  have hdescent : baseEnd_6827289 < baseStart_6827289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827290 : List Nat := [3, 1, 1, 3, 3, 2, 3, 1, 1, 5]
def baseStart_6827290 : Nat := 118140960795 + 6827290 * 2 ^ 59
def prefixEnd_6827290 : Nat := 4983230072969 + 3 ^ 40 * 6827290 * 2
def baseEnd_6827290 : Nat := 1168560445878232810058957

theorem tailTrace_6827290 : CollatzResearch.WordTrace tailWord_6827290 prefixEnd_6827290 1168560445878232810058957 := by
  unfold tailWord_6827290
  simp only [CollatzResearch.WordTrace]
  refine ⟨62252930858975453286611831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166007815623934542097631549 62252930858975453286611831)
  ·
    refine ⟨93379396288463179929917747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62252930858975453286611831 93379396288463179929917747)
    ·
      refine ⟨140069094432694769894876621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93379396288463179929917747 140069094432694769894876621)
      ·
        refine ⟨52525910412260538710578733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140069094432694769894876621 52525910412260538710578733)
        ·
          refine ⟨19697216404597702016467025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52525910412260538710578733 19697216404597702016467025)
          ·
            refine ⟨14772912303448276512350269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19697216404597702016467025 14772912303448276512350269)
            ·
              refine ⟨5539842113793103692131351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14772912303448276512350269 5539842113793103692131351)
              ·
                refine ⟨8309763170689655538197027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5539842113793103692131351 8309763170689655538197027)
                ·
                  refine ⟨12464644756034483307295541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8309763170689655538197027 12464644756034483307295541)
                  ·
                    refine ⟨1168560445878232810058957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12464644756034483307295541 1168560445878232810058957)
                    ·
                      rfl

theorem cell23_6827290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 1, 5].length) (baseStart_6827290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827290 prefixEnd_6827290 := by exact prefixLift 6827290
  have htrace : WordTrace (prefixWord ++ tailWord_6827290) baseStart_6827290 baseEnd_6827290 := by
    simpa [prefixWord, tailWord_6827290, baseEnd_6827290] using wordTrace_append hprefix tailTrace_6827290
  have hstable : (prefixWord ++ tailWord_6827290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827290).length < 2 ^ (prefixWord ++ tailWord_6827290).sum := by decide
  have hdescent : baseEnd_6827290 < baseStart_6827290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827299 : List Nat := [1, 1, 1, 4, 2, 14]
def baseStart_6827299 : Nat := 118140960795 + 6827299 * 2 ^ 59
def prefixEnd_6827299 : Nat := 4983230072969 + 3 ^ 40 * 6827299 * 2
def baseEnd_6827299 : Nat := 14426691189138225905203

theorem tailTrace_6827299 : CollatzResearch.WordTrace tailWord_6827299 prefixEnd_6827299 14426691189138225905203 := by
  unfold tailWord_6827299
  simp only [CollatzResearch.WordTrace]
  refine ⟨249012051692869207683524951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166008034461912805122349967 249012051692869207683524951)
  ·
    refine ⟨373518077539303811525287427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249012051692869207683524951 373518077539303811525287427)
    ·
      refine ⟨560277116308955717287931141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373518077539303811525287427 560277116308955717287931141)
      ·
        refine ⟨105051959307929196991487089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 560277116308955717287931141 105051959307929196991487089)
        ·
          refine ⟨78788969480946897743615317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105051959307929196991487089 78788969480946897743615317)
          ·
            refine ⟨14426691189138225905203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 78788969480946897743615317 14426691189138225905203)
            ·
              rfl

theorem cell23_6827299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 14].length) (baseStart_6827299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827299 prefixEnd_6827299 := by exact prefixLift 6827299
  have htrace : WordTrace (prefixWord ++ tailWord_6827299) baseStart_6827299 baseEnd_6827299 := by
    simpa [prefixWord, tailWord_6827299, baseEnd_6827299] using wordTrace_append hprefix tailTrace_6827299
  have hstable : (prefixWord ++ tailWord_6827299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827299).length < 2 ^ (prefixWord ++ tailWord_6827299).sum := by decide
  have hdescent : baseEnd_6827299 < baseStart_6827299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827304 : List Nat := [2, 1, 5, 1, 2, 1, 4, 2, 1, 1, 3]
def baseStart_6827304 : Nat := 118140960795 + 6827304 * 2 ^ 59
def prefixEnd_6827304 : Nat := 4983230072969 + 3 ^ 40 * 6827304 * 2
def baseEnd_6827304 : Nat := 3505688526363861375401807

theorem tailTrace_6827304 : CollatzResearch.WordTrace tailWord_6827304 prefixEnd_6827304 3505688526363861375401807 := by
  unfold tailWord_6827304
  simp only [CollatzResearch.WordTrace]
  refine ⟨124506117028925546768728483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166008156038567395691637977 124506117028925546768728483)
  ·
    refine ⟨186759175543388320153092725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124506117028925546768728483 186759175543388320153092725)
    ·
      refine ⟨17508672707192655014352443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 186759175543388320153092725 17508672707192655014352443)
      ·
        refine ⟨26263009060788982521528665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17508672707192655014352443 26263009060788982521528665)
        ·
          refine ⟨19697256795591736891146499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26263009060788982521528665 19697256795591736891146499)
          ·
            refine ⟨29545885193387605336719749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19697256795591736891146499 29545885193387605336719749)
            ·
              refine ⟨5539853473760176000634953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29545885193387605336719749 5539853473760176000634953)
              ·
                refine ⟨4154890105320132000476215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5539853473760176000634953 4154890105320132000476215)
                ·
                  refine ⟨6232335157980198000714323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4154890105320132000476215 6232335157980198000714323)
                  ·
                    refine ⟨9348502736970297001071485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6232335157980198000714323 9348502736970297001071485)
                    ·
                      refine ⟨3505688526363861375401807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9348502736970297001071485 3505688526363861375401807)
                      ·
                        rfl

theorem cell23_6827304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_6827304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827304 prefixEnd_6827304 := by exact prefixLift 6827304
  have htrace : WordTrace (prefixWord ++ tailWord_6827304) baseStart_6827304 baseEnd_6827304 := by
    simpa [prefixWord, tailWord_6827304, baseEnd_6827304] using wordTrace_append hprefix tailTrace_6827304
  have hstable : (prefixWord ++ tailWord_6827304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827304).length < 2 ^ (prefixWord ++ tailWord_6827304).sum := by decide
  have hdescent : baseEnd_6827304 < baseStart_6827304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827313 : List Nat := [1, 2, 2, 3, 3, 1, 1, 2, 3, 2, 3]
def baseStart_6827313 : Nat := 118140960795 + 6827313 * 2 ^ 59
def prefixEnd_6827313 : Nat := 4983230072969 + 3 ^ 40 * 6827313 * 2
def baseEnd_6827313 : Nat := 3505693147689751840189265

theorem tailTrace_6827313 : CollatzResearch.WordTrace tailWord_6827313 prefixEnd_6827313 3505693147689751840189265 := by
  unfold tailWord_6827313
  simp only [CollatzResearch.WordTrace]
  refine ⟨249012562314818488074534593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166008374876545658716356395 249012562314818488074534593)
  ·
    refine ⟨186759421736113866055900945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249012562314818488074534593 186759421736113866055900945)
    ·
      refine ⟨140069566302085399541925709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186759421736113866055900945 140069566302085399541925709)
      ·
        refine ⟨52526087363282024828222141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140069566302085399541925709 52526087363282024828222141)
        ·
          refine ⟨19697282761230759310583303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52526087363282024828222141 19697282761230759310583303)
          ·
            refine ⟨29545924141846138965874955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19697282761230759310583303 29545924141846138965874955)
            ·
              refine ⟨44318886212769208448812433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29545924141846138965874955 44318886212769208448812433)
              ·
                refine ⟨33239164659576906336609325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44318886212769208448812433 33239164659576906336609325)
                ·
                  refine ⟨12464686747341339876228497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33239164659576906336609325 12464686747341339876228497)
                  ·
                    refine ⟨9348515060506004907171373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12464686747341339876228497 9348515060506004907171373)
                    ·
                      refine ⟨3505693147689751840189265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9348515060506004907171373 3505693147689751840189265)
                      ·
                        rfl

theorem cell23_6827313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_6827313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827313 prefixEnd_6827313 := by exact prefixLift 6827313
  have htrace : WordTrace (prefixWord ++ tailWord_6827313) baseStart_6827313 baseEnd_6827313 := by
    simpa [prefixWord, tailWord_6827313, baseEnd_6827313] using wordTrace_append hprefix tailTrace_6827313
  have hstable : (prefixWord ++ tailWord_6827313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827313).length < 2 ^ (prefixWord ++ tailWord_6827313).sum := by decide
  have hdescent : baseEnd_6827313 < baseStart_6827313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827341 : List Nat := [1, 6, 1, 3, 2, 1, 2, 1, 1, 5]
def baseStart_6827341 : Nat := 118140960795 + 6827341 * 2 ^ 59
def prefixEnd_6827341 : Nat := 4983230072969 + 3 ^ 40 * 6827341 * 2
def baseEnd_6827341 : Nat := 1168569175049359243546379

theorem tailTrace_6827341 : CollatzResearch.WordTrace tailWord_6827341 prefixEnd_6827341 1168569175049359243546379 := by
  unfold tailWord_6827341
  simp only [CollatzResearch.WordTrace]
  refine ⟨249013583558717048856553877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166009055705811365904369251 249013583558717048856553877)
  ·
    refine ⟨11672511729314861665150963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 249013583558717048856553877 11672511729314861665150963)
    ·
      refine ⟨17508767593972292497726445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11672511729314861665150963 17508767593972292497726445)
      ·
        refine ⟨6565787847739609686647417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17508767593972292497726445 6565787847739609686647417)
        ·
          refine ⟨4924340885804707264985563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6565787847739609686647417 4924340885804707264985563)
          ·
            refine ⟨7386511328707060897478345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4924340885804707264985563 7386511328707060897478345)
            ·
              refine ⟨5539883496530295673108759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7386511328707060897478345 5539883496530295673108759)
              ·
                refine ⟨8309825244795443509663139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5539883496530295673108759 8309825244795443509663139)
                ·
                  refine ⟨12464737867193165264494709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8309825244795443509663139 12464737867193165264494709)
                  ·
                    refine ⟨1168569175049359243546379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12464737867193165264494709 1168569175049359243546379)
                    ·
                      rfl

theorem cell23_6827341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_6827341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827341 prefixEnd_6827341 := by exact prefixLift 6827341
  have htrace : WordTrace (prefixWord ++ tailWord_6827341) baseStart_6827341 baseEnd_6827341 := by
    simpa [prefixWord, tailWord_6827341, baseEnd_6827341] using wordTrace_append hprefix tailTrace_6827341
  have hstable : (prefixWord ++ tailWord_6827341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827341).length < 2 ^ (prefixWord ++ tailWord_6827341).sum := by decide
  have hdescent : baseEnd_6827341 < baseStart_6827341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827360 : List Nat := [2, 1, 1, 3, 4, 2, 1, 1, 4, 1, 3]
def baseStart_6827360 : Nat := 118140960795 + 6827360 * 2 ^ 59
def prefixEnd_6827360 : Nat := 4983230072969 + 3 ^ 40 * 6827360 * 2
def baseEnd_6827360 : Nat := 3505717281280513156301549

theorem tailTrace_6827360 : CollatzResearch.WordTrace tailWord_6827360 prefixEnd_6827360 3505717281280513156301549 := by
  unfold tailWord_6827360
  simp only [CollatzResearch.WordTrace]
  refine ⟨124507138272824107550747767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166009517697098810067663689 124507138272824107550747767)
  ·
    refine ⟨186760707409236161326121651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124507138272824107550747767 186760707409236161326121651)
    ·
      refine ⟨280141061113854241989182477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186760707409236161326121651 280141061113854241989182477)
      ·
        refine ⟨105052897917695340745943429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280141061113854241989182477 105052897917695340745943429)
        ·
          refine ⟨19697418359567876389864393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105052897917695340745943429 19697418359567876389864393)
          ·
            refine ⟨14773063769675907292398295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19697418359567876389864393 14773063769675907292398295)
            ·
              refine ⟨22159595654513860938597443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14773063769675907292398295 22159595654513860938597443)
              ·
                refine ⟨33239393481770791407896165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22159595654513860938597443 33239393481770791407896165)
                ·
                  refine ⟨6232386277832023388980531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33239393481770791407896165 6232386277832023388980531)
                  ·
                    refine ⟨9348579416748035083470797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6232386277832023388980531 9348579416748035083470797)
                    ·
                      refine ⟨3505717281280513156301549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9348579416748035083470797 3505717281280513156301549)
                      ·
                        rfl

theorem cell23_6827360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_6827360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827360 prefixEnd_6827360 := by exact prefixLift 6827360
  have htrace : WordTrace (prefixWord ++ tailWord_6827360) baseStart_6827360 baseEnd_6827360 := by
    simpa [prefixWord, tailWord_6827360, baseEnd_6827360] using wordTrace_append hprefix tailTrace_6827360
  have hstable : (prefixWord ++ tailWord_6827360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827360).length < 2 ^ (prefixWord ++ tailWord_6827360).sum := by decide
  have hdescent : baseEnd_6827360 < baseStart_6827360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827374 : List Nat := [4, 1, 2, 4, 2, 1, 1, 1, 1, 2, 4]
def baseStart_6827374 : Nat := 118140960795 + 6827374 * 2 ^ 59
def prefixEnd_6827374 : Nat := 4983230072969 + 3 ^ 40 * 6827374 * 2
def baseEnd_6827374 : Nat := 3505724470009676101526485

theorem tailTrace_6827374 : CollatzResearch.WordTrace tailWord_6827374 prefixEnd_6827374 3505724470009676101526485 := by
  unfold tailWord_6827374
  simp only [CollatzResearch.WordTrace]
  refine ⟨31126848395949686936563147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166009858111731663661670117 31126848395949686936563147)
  ·
    refine ⟨46690272593924530404844721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31126848395949686936563147 46690272593924530404844721)
    ·
      refine ⟨35017704445443397803633541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46690272593924530404844721 35017704445443397803633541)
      ·
        refine ⟨6565819583520637088181289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35017704445443397803633541 6565819583520637088181289)
        ·
          refine ⟨4924364687640477816135967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6565819583520637088181289 4924364687640477816135967)
          ·
            refine ⟨7386547031460716724203951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4924364687640477816135967 7386547031460716724203951)
            ·
              refine ⟨11079820547191075086305927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7386547031460716724203951 11079820547191075086305927)
              ·
                refine ⟨16619730820786612629458891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11079820547191075086305927 16619730820786612629458891)
                ·
                  refine ⟨24929596231179918944188337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16619730820786612629458891 24929596231179918944188337)
                  ·
                    refine ⟨18697197173384939208141253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24929596231179918944188337 18697197173384939208141253)
                    ·
                      refine ⟨3505724470009676101526485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18697197173384939208141253 3505724470009676101526485)
                      ·
                        rfl

theorem cell23_6827374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_6827374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827374 prefixEnd_6827374 := by exact prefixLift 6827374
  have htrace : WordTrace (prefixWord ++ tailWord_6827374) baseStart_6827374 baseEnd_6827374 := by
    simpa [prefixWord, tailWord_6827374, baseEnd_6827374] using wordTrace_append hprefix tailTrace_6827374
  have hstable : (prefixWord ++ tailWord_6827374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827374).length < 2 ^ (prefixWord ++ tailWord_6827374).sum := by decide
  have hdescent : baseEnd_6827374 < baseStart_6827374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827376 : List Nat := [2, 1, 1, 1, 4, 2, 1, 3, 2, 6]
def baseStart_6827376 : Nat := 118140960795 + 6827376 * 2 ^ 59
def prefixEnd_6827376 : Nat := 4983230072969 + 3 ^ 40 * 6827376 * 2
def baseEnd_6827376 : Nat := 1168575165656995031233825

theorem tailTrace_6827376 : CollatzResearch.WordTrace tailWord_6827376 prefixEnd_6827376 1168575165656995031233825 := by
  unfold tailWord_6827376
  simp only [CollatzResearch.WordTrace]
  refine ⟨124507430056795124917038991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166009906742393499889385321 124507430056795124917038991)
  ·
    refine ⟨186761145085192687375558487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124507430056795124917038991 186761145085192687375558487)
    ·
      refine ⟨280141717627789031063337731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186761145085192687375558487 280141717627789031063337731)
      ·
        refine ⟨420212576441683546595006597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280141717627789031063337731 420212576441683546595006597)
        ·
          refine ⟨78789858082815664986563737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 420212576441683546595006597 78789858082815664986563737)
          ·
            refine ⟨59092393562111748739922803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78789858082815664986563737 59092393562111748739922803)
            ·
              refine ⟨88638590343167623109884205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59092393562111748739922803 88638590343167623109884205)
              ·
                refine ⟨33239471378687858666206577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88638590343167623109884205 33239471378687858666206577)
                ·
                  refine ⟨24929603534015893999654933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33239471378687858666206577 24929603534015893999654933)
                  ·
                    refine ⟨1168575165656995031233825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24929603534015893999654933 1168575165656995031233825)
                    ·
                      rfl

theorem cell23_6827376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 2, 6].length) (baseStart_6827376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827376 prefixEnd_6827376 := by exact prefixLift 6827376
  have htrace : WordTrace (prefixWord ++ tailWord_6827376) baseStart_6827376 baseEnd_6827376 := by
    simpa [prefixWord, tailWord_6827376, baseEnd_6827376] using wordTrace_append hprefix tailTrace_6827376
  have hstable : (prefixWord ++ tailWord_6827376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827376).length < 2 ^ (prefixWord ++ tailWord_6827376).sum := by decide
  have hdescent : baseEnd_6827376 < baseStart_6827376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827386 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 4, 1, 5]
def baseStart_6827386 : Nat := 118140960795 + 6827386 * 2 ^ 59
def prefixEnd_6827386 : Nat := 4983230072969 + 3 ^ 40 * 6827386 * 2
def baseEnd_6827386 : Nat := 3505730631777530054576429

theorem tailTrace_6827386 : CollatzResearch.WordTrace tailWord_6827386 prefixEnd_6827386 3505730631777530054576429 := by
  unfold tailWord_6827386
  simp only [CollatzResearch.WordTrace]
  refine ⟨62253806210888505385485503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166010149895702681027961341 62253806210888505385485503)
  ·
    refine ⟨93380709316332758078228255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62253806210888505385485503 93380709316332758078228255)
    ·
      refine ⟨140071063974499137117342383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93380709316332758078228255 140071063974499137117342383)
      ·
        refine ⟨210106595961748705676013575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140071063974499137117342383 210106595961748705676013575)
        ·
          refine ⟨315159893942623058514020363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210106595961748705676013575 315159893942623058514020363)
          ·
            refine ⟨472739840913934587771030545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315159893942623058514020363 472739840913934587771030545)
            ·
              refine ⟨354554880685450940828272909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472739840913934587771030545 354554880685450940828272909)
              ·
                refine ⟨132958080257044102810602341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 354554880685450940828272909 132958080257044102810602341)
                ·
                  refine ⟨24929640048195769276987939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132958080257044102810602341 24929640048195769276987939)
                  ·
                    refine ⟨37394460072293653915481909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24929640048195769276987939 37394460072293653915481909)
                    ·
                      refine ⟨3505730631777530054576429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37394460072293653915481909 3505730631777530054576429)
                      ·
                        rfl

theorem cell23_6827386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_6827386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827386 prefixEnd_6827386 := by exact prefixLift 6827386
  have htrace : WordTrace (prefixWord ++ tailWord_6827386) baseStart_6827386 baseEnd_6827386 := by
    simpa [prefixWord, tailWord_6827386, baseEnd_6827386] using wordTrace_append hprefix tailTrace_6827386
  have hstable : (prefixWord ++ tailWord_6827386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827386).length < 2 ^ (prefixWord ++ tailWord_6827386).sum := by decide
  have hdescent : baseEnd_6827386 < baseStart_6827386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827423 : List Nat := [1, 1, 2, 5, 1, 2, 3, 1, 7]
def baseStart_6827423 : Nat := 118140960795 + 6827423 * 2 ^ 59
def prefixEnd_6827423 : Nat := 4983230072969 + 3 ^ 40 * 6827423 * 2
def baseEnd_6827423 : Nat := 389527736729082934423751

theorem tailTrace_6827423 : CollatzResearch.WordTrace tailWord_6827423 prefixEnd_6827423 389527736729082934423751 := by
  unfold tailWord_6827423
  simp only [CollatzResearch.WordTrace]
  refine ⟨249016574344419976861038923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166011049562946651240692615 249016574344419976861038923)
  ·
    refine ⟨373524861516629965291558385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249016574344419976861038923 373524861516629965291558385)
    ·
      refine ⟨280143646137472473968668789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373524861516629965291558385 280143646137472473968668789)
      ·
        refine ⟨26263466825388044434562699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 280143646137472473968668789 26263466825388044434562699)
        ·
          refine ⟨39395200238082066651844049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26263466825388044434562699 39395200238082066651844049)
          ·
            refine ⟨29546400178561549988883037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39395200238082066651844049 29546400178561549988883037)
            ·
              refine ⟨11079900066960581245831139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29546400178561549988883037 11079900066960581245831139)
              ·
                refine ⟨16619850100440871868746709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11079900066960581245831139 16619850100440871868746709)
                ·
                  refine ⟨389527736729082934423751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16619850100440871868746709 389527736729082934423751)
                  ·
                    rfl

theorem cell23_6827423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 7].length) (baseStart_6827423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827423 prefixEnd_6827423 := by exact prefixLift 6827423
  have htrace : WordTrace (prefixWord ++ tailWord_6827423) baseStart_6827423 baseEnd_6827423 := by
    simpa [prefixWord, tailWord_6827423, baseEnd_6827423] using wordTrace_append hprefix tailTrace_6827423
  have hstable : (prefixWord ++ tailWord_6827423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827423).length < 2 ^ (prefixWord ++ tailWord_6827423).sum := by decide
  have hdescent : baseEnd_6827423 < baseStart_6827423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827436 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 3, 7]
def baseStart_6827436 : Nat := 118140960795 + 6827436 * 2 ^ 59
def prefixEnd_6827436 : Nat := 4983230072969 + 3 ^ 40 * 6827436 * 2
def baseEnd_6827436 : Nat := 1168585435270084952983733

theorem tailTrace_6827436 : CollatzResearch.WordTrace tailWord_6827436 prefixEnd_6827436 1168585435270084952983733 := by
  unfold tailWord_6827436
  simp only [CollatzResearch.WordTrace]
  refine ⟨124508524246686440040631081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166011365662248586720841441 124508524246686440040631081)
  ·
    refine ⟨93381393185014830030473311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124508524246686440040631081 93381393185014830030473311)
    ·
      refine ⟨140072089777522245045709967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93381393185014830030473311 140072089777522245045709967)
      ·
        refine ⟨210108134666283367568564951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140072089777522245045709967 210108134666283367568564951)
        ·
          refine ⟨315162201999425051352847427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210108134666283367568564951 315162201999425051352847427)
          ·
            refine ⟨472743302999137577029271141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315162201999425051352847427 472743302999137577029271141)
            ·
              refine ⟨88639369312338295692988339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 472743302999137577029271141 88639369312338295692988339)
              ·
                refine ⟨132959053968507443539482509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88639369312338295692988339 132959053968507443539482509)
                ·
                  refine ⟨49859645238190291327305941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132959053968507443539482509 49859645238190291327305941)
                  ·
                    refine ⟨1168585435270084952983733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49859645238190291327305941 1168585435270084952983733)
                    ·
                      rfl

theorem cell23_6827436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 7].length) (baseStart_6827436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827436 prefixEnd_6827436 := by exact prefixLift 6827436
  have htrace : WordTrace (prefixWord ++ tailWord_6827436) baseStart_6827436 baseEnd_6827436 := by
    simpa [prefixWord, tailWord_6827436, baseEnd_6827436] using wordTrace_append hprefix tailTrace_6827436
  have hstable : (prefixWord ++ tailWord_6827436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827436).length < 2 ^ (prefixWord ++ tailWord_6827436).sum := by decide
  have hdescent : baseEnd_6827436 < baseStart_6827436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827517 : List Nat := [1, 4, 1, 1, 1, 4, 1, 5, 1, 4]
def baseStart_6827517 : Nat := 118140960795 + 6827517 * 2 ^ 59
def prefixEnd_6827517 : Nat := 4983230072969 + 3 ^ 40 * 6827517 * 2
def baseEnd_6827517 : Nat := 1168599299247756347346109

theorem tailTrace_6827517 : CollatzResearch.WordTrace tailWord_6827517 prefixEnd_6827517 1168599299247756347346109 := by
  unfold tailWord_6827517
  simp only [CollatzResearch.WordTrace]
  refine ⟨249020002806079430914960805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166013335204052953943307203 249020002806079430914960805)
  ·
    refine ⟨46691250526139893296555151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249020002806079430914960805 46691250526139893296555151)
    ·
      refine ⟨70036875789209839944832727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46691250526139893296555151 70036875789209839944832727)
      ·
        refine ⟨105055313683814759917249091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70036875789209839944832727 105055313683814759917249091)
        ·
          refine ⟨157582970525722139875873637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105055313683814759917249091 157582970525722139875873637)
          ·
            refine ⟨29546806973572901226726307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157582970525722139875873637 29546806973572901226726307)
            ·
              refine ⟨44320210460359351840089461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29546806973572901226726307 44320210460359351840089461)
              ·
                refine ⟨4155019730658689235008387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44320210460359351840089461 4155019730658689235008387)
                ·
                  refine ⟨6232529595988033852512581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4155019730658689235008387 6232529595988033852512581)
                  ·
                    refine ⟨1168599299247756347346109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6232529595988033852512581 1168599299247756347346109)
                    ·
                      rfl

theorem cell23_6827517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_6827517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827517 prefixEnd_6827517 := by exact prefixLift 6827517
  have htrace : WordTrace (prefixWord ++ tailWord_6827517) baseStart_6827517 baseEnd_6827517 := by
    simpa [prefixWord, tailWord_6827517, baseEnd_6827517] using wordTrace_append hprefix tailTrace_6827517
  have hstable : (prefixWord ++ tailWord_6827517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827517).length < 2 ^ (prefixWord ++ tailWord_6827517).sum := by decide
  have hdescent : baseEnd_6827517 < baseStart_6827517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827530 : List Nat := [3, 1, 2, 2, 2, 2, 3, 2, 6]
def baseStart_6827530 : Nat := 118140960795 + 6827530 * 2 ^ 59
def prefixEnd_6827530 : Nat := 4983230072969 + 3 ^ 40 * 6827530 * 2
def baseEnd_6827530 : Nat := 389533841443530832352863

theorem tailTrace_6827530 : CollatzResearch.WordTrace tailWord_6827530 prefixEnd_6827530 389533841443530832352863 := by
  unfold tailWord_6827530
  simp only [CollatzResearch.WordTrace]
  refine ⟨62255119238758083533796011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166013651303354889423456029 62255119238758083533796011)
  ·
    refine ⟨93382678858137125300694017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62255119238758083533796011 93382678858137125300694017)
    ·
      refine ⟨70037009143602843975520513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93382678858137125300694017 70037009143602843975520513)
      ·
        refine ⟨52527756857702132981640385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70037009143602843975520513 52527756857702132981640385)
        ·
          refine ⟨39395817643276599736230289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52527756857702132981640385 39395817643276599736230289)
          ·
            refine ⟨29546863232457449802172717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39395817643276599736230289 29546863232457449802172717)
            ·
              refine ⟨11080073712171543675814769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29546863232457449802172717 11080073712171543675814769)
              ·
                refine ⟨8310055284128657756861077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11080073712171543675814769 8310055284128657756861077)
                ·
                  refine ⟨389533841443530832352863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8310055284128657756861077 389533841443530832352863)
                  ·
                    rfl

theorem cell23_6827530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 6].length) (baseStart_6827530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827530 prefixEnd_6827530 := by exact prefixLift 6827530
  have htrace : WordTrace (prefixWord ++ tailWord_6827530) baseStart_6827530 baseEnd_6827530 := by
    simpa [prefixWord, tailWord_6827530, baseEnd_6827530] using wordTrace_append hprefix tailTrace_6827530
  have hstable : (prefixWord ++ tailWord_6827530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827530).length < 2 ^ (prefixWord ++ tailWord_6827530).sum := by decide
  have hdescent : baseEnd_6827530 < baseStart_6827530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827591 : List Nat := [1, 1, 4, 1, 6, 1, 1, 1, 3, 1, 3]
def baseStart_6827591 : Nat := 118140960795 + 6827591 * 2 ^ 59
def prefixEnd_6827591 : Nat := 4983230072969 + 3 ^ 40 * 6827591 * 2
def baseEnd_6827591 : Nat := 3505835895311701752512987

theorem tailTrace_6827591 : CollatzResearch.WordTrace tailWord_6827591 prefixEnd_6827591 3505835895311701752512987 := by
  unfold tailWord_6827591
  simp only [CollatzResearch.WordTrace]
  refine ⟨249022701807811341553154627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166015134538540894368769751 249022701807811341553154627)
  ·
    refine ⟨373534052711717012329731941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249022701807811341553154627 373534052711717012329731941)
    ·
      refine ⟨70037634883446939811824739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 373534052711717012329731941 70037634883446939811824739)
      ·
        refine ⟨105056452325170409717737109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70037634883446939811824739 105056452325170409717737109)
        ·
          refine ⟨4924521202742362955518927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 105056452325170409717737109 4924521202742362955518927)
          ·
            refine ⟨7386781804113544433278391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4924521202742362955518927 7386781804113544433278391)
            ·
              refine ⟨11080172706170316649917587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7386781804113544433278391 11080172706170316649917587)
              ·
                refine ⟨16620259059255474974876381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11080172706170316649917587 16620259059255474974876381)
                ·
                  refine ⟨6232597147220803115578643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16620259059255474974876381 6232597147220803115578643)
                  ·
                    refine ⟨9348895720831204673367965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6232597147220803115578643 9348895720831204673367965)
                    ·
                      refine ⟨3505835895311701752512987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9348895720831204673367965 3505835895311701752512987)
                      ·
                        rfl

theorem cell23_6827591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 3, 1, 3].length) (baseStart_6827591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827591 prefixEnd_6827591 := by exact prefixLift 6827591
  have htrace : WordTrace (prefixWord ++ tailWord_6827591) baseStart_6827591 baseEnd_6827591 := by
    simpa [prefixWord, tailWord_6827591, baseEnd_6827591] using wordTrace_append hprefix tailTrace_6827591
  have hstable : (prefixWord ++ tailWord_6827591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827591).length < 2 ^ (prefixWord ++ tailWord_6827591).sum := by decide
  have hdescent : baseEnd_6827591 < baseStart_6827591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827600 : List Nat := [2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 3]
def baseStart_6827600 : Nat := 118140960795 + 6827600 * 2 ^ 59
def prefixEnd_6827600 : Nat := 4983230072969 + 3 ^ 40 * 6827600 * 2
def baseEnd_6827600 : Nat := 3505840516637592217300445

theorem tailTrace_6827600 : CollatzResearch.WordTrace tailWord_6827600 prefixEnd_6827600 3505840516637592217300445 := by
  unfold tailWord_6827600
  simp only [CollatzResearch.WordTrace]
  refine ⟨124511515032389368045116127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166015353376519157393488169 124511515032389368045116127)
  ·
    refine ⟨186767272548584052067674191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124511515032389368045116127 186767272548584052067674191)
    ·
      refine ⟨280150908822876078101511287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186767272548584052067674191 280150908822876078101511287)
      ·
        refine ⟨420226363234314117152266931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280150908822876078101511287 420226363234314117152266931)
        ·
          refine ⟨630339544851471175728400397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420226363234314117152266931 630339544851471175728400397)
          ·
            refine ⟨236377329319301690898150149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 630339544851471175728400397 236377329319301690898150149)
            ·
              refine ⟨44320749247369067043403153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 236377329319301690898150149 44320749247369067043403153)
              ·
                refine ⟨33240561935526800282552365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44320749247369067043403153 33240561935526800282552365)
                ·
                  refine ⟨12465210725822550105957137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33240561935526800282552365 12465210725822550105957137)
                  ·
                    refine ⟨9348908044366912579467853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12465210725822550105957137 9348908044366912579467853)
                    ·
                      refine ⟨3505840516637592217300445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9348908044366912579467853 3505840516637592217300445)
                      ·
                        rfl

theorem cell23_6827600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 3].length) (baseStart_6827600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827600 prefixEnd_6827600 := by exact prefixLift 6827600
  have htrace : WordTrace (prefixWord ++ tailWord_6827600) baseStart_6827600 baseEnd_6827600 := by
    simpa [prefixWord, tailWord_6827600, baseEnd_6827600] using wordTrace_append hprefix tailTrace_6827600
  have hstable : (prefixWord ++ tailWord_6827600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827600).length < 2 ^ (prefixWord ++ tailWord_6827600).sum := by decide
  have hdescent : baseEnd_6827600 < baseStart_6827600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827607 : List Nat := [1, 1, 3, 2, 2, 4, 1, 3, 2, 4]
def baseStart_6827607 : Nat := 118140960795 + 6827607 * 2 ^ 59
def prefixEnd_6827607 : Nat := 4983230072969 + 3 ^ 40 * 6827607 * 2
def baseEnd_6827607 : Nat := 1168614703667391229970971

theorem tailTrace_6827607 : CollatzResearch.WordTrace tailWord_6827607 prefixEnd_6827607 1168614703667391229970971 := by
  unfold tailWord_6827607
  simp only [CollatzResearch.WordTrace]
  refine ⟨249023285375753376285737075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166015523583835584190491383 249023285375753376285737075)
  ·
    refine ⟨373534928063630064428605613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249023285375753376285737075 373534928063630064428605613)
    ·
      refine ⟨140075598023861274160727105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373534928063630064428605613 140075598023861274160727105)
      ·
        refine ⟨105056698517895955620545329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140075598023861274160727105 105056698517895955620545329)
        ·
          refine ⟨78792523888421966715408997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105056698517895955620545329 78792523888421966715408997)
          ·
            refine ⟨14773598229079118759139187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78792523888421966715408997 14773598229079118759139187)
            ·
              refine ⟨22160397343618678138708781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14773598229079118759139187 22160397343618678138708781)
              ·
                refine ⟨8310149003857004302015793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22160397343618678138708781 8310149003857004302015793)
                ·
                  refine ⟨6232611752892753226511845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8310149003857004302015793 6232611752892753226511845)
                  ·
                    refine ⟨1168614703667391229970971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6232611752892753226511845 1168614703667391229970971)
                    ·
                      rfl

theorem cell23_6827607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 2, 4].length) (baseStart_6827607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827607 prefixEnd_6827607 := by exact prefixLift 6827607
  have htrace : WordTrace (prefixWord ++ tailWord_6827607) baseStart_6827607 baseEnd_6827607 := by
    simpa [prefixWord, tailWord_6827607, baseEnd_6827607] using wordTrace_append hprefix tailTrace_6827607
  have hstable : (prefixWord ++ tailWord_6827607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827607).length < 2 ^ (prefixWord ++ tailWord_6827607).sum := by decide
  have hdescent : baseEnd_6827607 < baseStart_6827607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827633 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 4, 7]
def baseStart_6827633 : Nat := 118140960795 + 6827633 * 2 ^ 59
def prefixEnd_6827633 : Nat := 4983230072969 + 3 ^ 40 * 6827633 * 2
def baseEnd_6827633 : Nat := 1168619153833063529395931

theorem tailTrace_6827633 : CollatzResearch.WordTrace tailWord_6827633 prefixEnd_6827633 1168619153833063529395931 := by
  unfold tailWord_6827633
  simp only [CollatzResearch.WordTrace]
  refine ⟨249024233673659182726183553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166016155782439455150789035 249024233673659182726183553)
  ·
    refine ⟨186768175255244387044637665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249024233673659182726183553 186768175255244387044637665)
    ·
      refine ⟨140076131441433290283478249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186768175255244387044637665 140076131441433290283478249)
      ·
        refine ⟨105057098581074967712608687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140076131441433290283478249 105057098581074967712608687)
        ·
          refine ⟨157585647871612451568913031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105057098581074967712608687 157585647871612451568913031)
          ·
            refine ⟨236378471807418677353369547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157585647871612451568913031 236378471807418677353369547)
            ·
              refine ⟨354567707711128016030054321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236378471807418677353369547 354567707711128016030054321)
              ·
                refine ⟨265925780783346012022540741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354567707711128016030054321 265925780783346012022540741)
                ·
                  refine ⟨49861083896877377254226389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 265925780783346012022540741 49861083896877377254226389)
                  ·
                    refine ⟨1168619153833063529395931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49861083896877377254226389 1168619153833063529395931)
                    ·
                      rfl

theorem cell23_6827633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 7].length) (baseStart_6827633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827633 prefixEnd_6827633 := by exact prefixLift 6827633
  have htrace : WordTrace (prefixWord ++ tailWord_6827633) baseStart_6827633 baseEnd_6827633 := by
    simpa [prefixWord, tailWord_6827633, baseEnd_6827633] using wordTrace_append hprefix tailTrace_6827633
  have hstable : (prefixWord ++ tailWord_6827633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827633).length < 2 ^ (prefixWord ++ tailWord_6827633).sum := by decide
  have hdescent : baseEnd_6827633 < baseStart_6827633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827657 : List Nat := [1, 2, 1, 1, 4, 1, 3, 2, 3, 3, 2]
def baseStart_6827657 : Nat := 118140960795 + 6827657 * 2 ^ 59
def prefixEnd_6827657 : Nat := 4983230072969 + 3 ^ 40 * 6827657 * 2
def baseEnd_6827657 : Nat := 3505869785034898494287683

theorem tailTrace_6827657 : CollatzResearch.WordTrace tailWord_6827657 prefixEnd_6827657 3505869785034898494287683 := by
  unfold tailWord_6827657
  simp only [CollatzResearch.WordTrace]
  refine ⟨249025109025572234825057225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166016739350381489883371483 249025109025572234825057225)
  ·
    refine ⟨186768831769179176118792919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249025109025572234825057225 186768831769179176118792919)
    ·
      refine ⟨280153247653768764178189379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186768831769179176118792919 280153247653768764178189379)
      ·
        refine ⟨420229871480653146267284069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280153247653768764178189379 420229871480653146267284069)
        ·
          refine ⟨78793100902622464925115763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 420229871480653146267284069 78793100902622464925115763)
          ·
            refine ⟨118189651353933697387673645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78793100902622464925115763 118189651353933697387673645)
            ·
              refine ⟨44321119257725136520377617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118189651353933697387673645 44321119257725136520377617)
              ·
                refine ⟨33240839443293852390283213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44321119257725136520377617 33240839443293852390283213)
                ·
                  refine ⟨12465314791235194646356205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33240839443293852390283213 12465314791235194646356205)
                  ·
                    refine ⟨4674493046713197992383577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12465314791235194646356205 4674493046713197992383577)
                    ·
                      refine ⟨3505869785034898494287683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4674493046713197992383577 3505869785034898494287683)
                      ·
                        rfl

theorem cell23_6827657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 3, 2].length) (baseStart_6827657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827657 prefixEnd_6827657 := by exact prefixLift 6827657
  have htrace : WordTrace (prefixWord ++ tailWord_6827657) baseStart_6827657 baseEnd_6827657 := by
    simpa [prefixWord, tailWord_6827657, baseEnd_6827657] using wordTrace_append hprefix tailTrace_6827657
  have hstable : (prefixWord ++ tailWord_6827657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827657).length < 2 ^ (prefixWord ++ tailWord_6827657).sum := by decide
  have hdescent : baseEnd_6827657 < baseStart_6827657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827757 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 4, 5]
def baseStart_6827757 : Nat := 118140960795 + 6827757 * 2 ^ 59
def prefixEnd_6827757 : Nat := 4983230072969 + 3 ^ 40 * 6827757 * 2
def baseEnd_6827757 : Nat := 1168640377700116034345741

theorem tailTrace_6827757 : CollatzResearch.WordTrace tailWord_6827757 prefixEnd_6827757 1168640377700116034345741 := by
  unfold tailWord_6827757
  simp only [CollatzResearch.WordTrace]
  refine ⟨249028756325209951903697525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166019170883473301269131683 249028756325209951903697525)
  ·
    refine ⟨23346445905488432990971643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 249028756325209951903697525 23346445905488432990971643)
    ·
      refine ⟨35019668858232649486457465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23346445905488432990971643 35019668858232649486457465)
      ·
        refine ⟨26264751643674487114843099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35019668858232649486457465 26264751643674487114843099)
        ·
          refine ⟨39397127465511730672264649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26264751643674487114843099 39397127465511730672264649)
          ·
            refine ⟨29547845599133798004198487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39397127465511730672264649 29547845599133798004198487)
            ·
              refine ⟨44321768398700697006297731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29547845599133798004198487 44321768398700697006297731)
              ·
                refine ⟨66482652598051045509446597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44321768398700697006297731 66482652598051045509446597)
                ·
                  refine ⟨12465497362134571033021237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66482652598051045509446597 12465497362134571033021237)
                  ·
                    refine ⟨1168640377700116034345741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12465497362134571033021237 1168640377700116034345741)
                    ·
                      rfl

theorem cell23_6827757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_6827757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827757 prefixEnd_6827757 := by exact prefixLift 6827757
  have htrace : WordTrace (prefixWord ++ tailWord_6827757) baseStart_6827757 baseEnd_6827757 := by
    simpa [prefixWord, tailWord_6827757, baseEnd_6827757] using wordTrace_append hprefix tailTrace_6827757
  have hstable : (prefixWord ++ tailWord_6827757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827757).length < 2 ^ (prefixWord ++ tailWord_6827757).sum := by decide
  have hdescent : baseEnd_6827757 < baseStart_6827757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827760 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 4]
def baseStart_6827760 : Nat := 118140960795 + 6827760 * 2 ^ 59
def prefixEnd_6827760 : Nat := 4983230072969 + 3 ^ 40 * 6827760 * 2
def baseEnd_6827760 : Nat := 3505922673542311591299709

theorem tailTrace_6827760 : CollatzResearch.WordTrace tailWord_6827760 prefixEnd_6827760 3505922673542311591299709 := by
  unfold tailWord_6827760
  simp only [CollatzResearch.WordTrace]
  refine ⟨124514432872099541708028367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166019243829466055610704489 124514432872099541708028367)
  ·
    refine ⟨186771649308149312562042551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124514432872099541708028367 186771649308149312562042551)
    ·
      refine ⟨280157473962223968843063827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186771649308149312562042551 280157473962223968843063827)
      ·
        refine ⟨420236210943335953264595741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280157473962223968843063827 420236210943335953264595741)
        ·
          refine ⟨157588579103750982474223403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 420236210943335953264595741 157588579103750982474223403)
          ·
            refine ⟨236382868655626473711335105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157588579103750982474223403 236382868655626473711335105)
            ·
              refine ⟨177287151491719855283501329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236382868655626473711335105 177287151491719855283501329)
              ·
                refine ⟨132965363618789891462625997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177287151491719855283501329 132965363618789891462625997)
                ·
                  refine ⟨49862011357046209298484749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132965363618789891462625997 49862011357046209298484749)
                  ·
                    refine ⟨18698254258892328486931781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49862011357046209298484749 18698254258892328486931781)
                    ·
                      refine ⟨3505922673542311591299709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18698254258892328486931781 3505922673542311591299709)
                      ·
                        rfl

theorem cell23_6827760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 4].length) (baseStart_6827760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827760 prefixEnd_6827760 := by exact prefixLift 6827760
  have htrace : WordTrace (prefixWord ++ tailWord_6827760) baseStart_6827760 baseEnd_6827760 := by
    simpa [prefixWord, tailWord_6827760, baseEnd_6827760] using wordTrace_append hprefix tailTrace_6827760
  have hstable : (prefixWord ++ tailWord_6827760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827760).length < 2 ^ (prefixWord ++ tailWord_6827760).sum := by decide
  have hdescent : baseEnd_6827760 < baseStart_6827760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827787 : List Nat := [1, 1, 1, 1, 5, 1, 2, 4, 3, 4]
def baseStart_6827787 : Nat := 118140960795 + 6827787 * 2 ^ 59
def prefixEnd_6827787 : Nat := 4983230072969 + 3 ^ 40 * 6827787 * 2
def baseEnd_6827787 : Nat := 1168645512506660995220695

theorem tailTrace_6827787 : CollatzResearch.WordTrace tailWord_6827787 prefixEnd_6827787 1168645512506660995220695 := by
  unfold tailWord_6827787
  simp only [CollatzResearch.WordTrace]
  refine ⟨249029850515101267027289615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166019900343400844684859743 249029850515101267027289615)
  ·
    refine ⟨373544775772651900540934423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249029850515101267027289615 373544775772651900540934423)
    ·
      refine ⟨560317163658977850811401635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373544775772651900540934423 560317163658977850811401635)
      ·
        refine ⟨840475745488466776217102453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560317163658977850811401635 840475745488466776217102453)
        ·
          refine ⟨78794601139543760270353355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 840475745488466776217102453 78794601139543760270353355)
          ·
            refine ⟨118191901709315640405530033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78794601139543760270353355 118191901709315640405530033)
            ·
              refine ⟨88643926281986730304147525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118191901709315640405530033 88643926281986730304147525)
              ·
                refine ⟨16620736177872511932027661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88643926281986730304147525 16620736177872511932027661)
                ·
                  refine ⟨6232776066702191974510373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16620736177872511932027661 6232776066702191974510373)
                  ·
                    refine ⟨1168645512506660995220695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6232776066702191974510373 1168645512506660995220695)
                    ·
                      rfl

theorem cell23_6827787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 3, 4].length) (baseStart_6827787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827787 prefixEnd_6827787 := by exact prefixLift 6827787
  have htrace : WordTrace (prefixWord ++ tailWord_6827787) baseStart_6827787 baseEnd_6827787 := by
    simpa [prefixWord, tailWord_6827787, baseEnd_6827787] using wordTrace_append hprefix tailTrace_6827787
  have hstable : (prefixWord ++ tailWord_6827787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827787).length < 2 ^ (prefixWord ++ tailWord_6827787).sum := by decide
  have hdescent : baseEnd_6827787 < baseStart_6827787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827800 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 10]
def baseStart_6827800 : Nat := 118140960795 + 6827800 * 2 ^ 59
def prefixEnd_6827800 : Nat := 4983230072969 + 3 ^ 40 * 6827800 * 2
def baseEnd_6827800 : Nat := 389549245863165714977725

theorem tailTrace_6827800 : CollatzResearch.WordTrace tailWord_6827800 prefixEnd_6827800 389549245863165714977725 := by
  unfold tailWord_6827800
  simp only [CollatzResearch.WordTrace]
  refine ⟨124515162332027085123756427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166020216442702780165008569 124515162332027085123756427)
  ·
    refine ⟨186772743498040627685634641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124515162332027085123756427 186772743498040627685634641)
    ·
      refine ⟨140079557623530470764225981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186772743498040627685634641 140079557623530470764225981)
      ·
        refine ⟨52529834108823926536584743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140079557623530470764225981 52529834108823926536584743)
        ·
          refine ⟨78794751163235889804877115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52529834108823926536584743 78794751163235889804877115)
          ·
            refine ⟨118192126744853834707315673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78794751163235889804877115 118192126744853834707315673)
            ·
              refine ⟨88644095058640376030486755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118192126744853834707315673 88644095058640376030486755)
              ·
                refine ⟨132966142587960564045730133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88644095058640376030486755 132966142587960564045730133)
                ·
                  refine ⟨389549245863165714977725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 132966142587960564045730133 389549245863165714977725)
                  ·
                    rfl

theorem cell23_6827800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 10].length) (baseStart_6827800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827800 prefixEnd_6827800 := by exact prefixLift 6827800
  have htrace : WordTrace (prefixWord ++ tailWord_6827800) baseStart_6827800 baseEnd_6827800 := by
    simpa [prefixWord, tailWord_6827800, baseEnd_6827800] using wordTrace_append hprefix tailTrace_6827800
  have hstable : (prefixWord ++ tailWord_6827800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827800).length < 2 ^ (prefixWord ++ tailWord_6827800).sum := by decide
  have hdescent : baseEnd_6827800 < baseStart_6827800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827847 : List Nat := [1, 1, 4, 1, 2, 1, 4, 1, 3, 5]
def baseStart_6827847 : Nat := 118140960795 + 6827847 * 2 ^ 59
def prefixEnd_6827847 : Nat := 4983230072969 + 3 ^ 40 * 6827847 * 2
def baseEnd_6827847 : Nat := 1168655782119750916970603

theorem tailTrace_6827847 : CollatzResearch.WordTrace tailWord_6827847 prefixEnd_6827847 1168655782119750916970603 := by
  unfold tailWord_6827847
  simp only [CollatzResearch.WordTrace]
  refine ⟨249032038894883897274473795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166021359263255931516315863 249032038894883897274473795)
  ·
    refine ⟨373548058342325845911710693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249032038894883897274473795 373548058342325845911710693)
    ·
      refine ⟨70040260939186096108445755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 373548058342325845911710693 70040260939186096108445755)
      ·
        refine ⟨105060391408779144162668633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70040260939186096108445755 105060391408779144162668633)
        ·
          refine ⟨78795293556584358122001475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105060391408779144162668633 78795293556584358122001475)
          ·
            refine ⟨118192940334876537183002213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78795293556584358122001475 118192940334876537183002213)
            ·
              refine ⟨22161176312789350721812915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118192940334876537183002213 22161176312789350721812915)
              ·
                refine ⟨33241764469184026082719373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22161176312789350721812915 33241764469184026082719373)
                ·
                  refine ⟨12465661675944009781019765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33241764469184026082719373 12465661675944009781019765)
                  ·
                    refine ⟨1168655782119750916970603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12465661675944009781019765 1168655782119750916970603)
                    ·
                      rfl

theorem cell23_6827847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_6827847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827847 prefixEnd_6827847 := by exact prefixLift 6827847
  have htrace : WordTrace (prefixWord ++ tailWord_6827847) baseStart_6827847 baseEnd_6827847 := by
    simpa [prefixWord, tailWord_6827847, baseEnd_6827847] using wordTrace_append hprefix tailTrace_6827847
  have hstable : (prefixWord ++ tailWord_6827847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827847).length < 2 ^ (prefixWord ++ tailWord_6827847).sum := by decide
  have hdescent : baseEnd_6827847 < baseStart_6827847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827868 : List Nat := [2, 2, 4, 2, 3, 1, 1, 2, 6]
def baseStart_6827868 : Nat := 118140960795 + 6827868 * 2 ^ 59
def prefixEnd_6827868 : Nat := 4983230072969 + 3 ^ 40 * 6827868 * 2
def baseEnd_6827868 : Nat := 389553125494777463194357

theorem tailTrace_6827868 : CollatzResearch.WordTrace tailWord_6827868 prefixEnd_6827868 389553125494777463194357 := by
  unfold tailWord_6827868
  simp only [CollatzResearch.WordTrace]
  refine ⟨124516402413903908930494129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166021869885205211907325505 124516402413903908930494129)
  ·
    refine ⟨93387301810427931697870597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124516402413903908930494129 93387301810427931697870597)
    ·
      refine ⟨17510119089455237193350737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93387301810427931697870597 17510119089455237193350737)
      ·
        refine ⟨13132589317091427895013053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17510119089455237193350737 13132589317091427895013053)
        ·
          refine ⟨4924720993909285460629895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13132589317091427895013053 4924720993909285460629895)
          ·
            refine ⟨7387081490863928190944843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4924720993909285460629895 7387081490863928190944843)
            ·
              refine ⟨11080622236295892286417265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7387081490863928190944843 11080622236295892286417265)
              ·
                refine ⟨8310466677221919214812949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11080622236295892286417265 8310466677221919214812949)
                ·
                  refine ⟨389553125494777463194357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8310466677221919214812949 389553125494777463194357)
                  ·
                    rfl

theorem cell23_6827868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 6].length) (baseStart_6827868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827868 prefixEnd_6827868 := by exact prefixLift 6827868
  have htrace : WordTrace (prefixWord ++ tailWord_6827868) baseStart_6827868 baseEnd_6827868 := by
    simpa [prefixWord, tailWord_6827868, baseEnd_6827868] using wordTrace_append hprefix tailTrace_6827868
  have hstable : (prefixWord ++ tailWord_6827868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827868).length < 2 ^ (prefixWord ++ tailWord_6827868).sum := by decide
  have hdescent : baseEnd_6827868 < baseStart_6827868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827897 : List Nat := [1, 2, 1, 3, 2, 2, 3, 1, 1, 1, 6]
def baseStart_6827897 : Nat := 118140960795 + 6827897 * 2 ^ 59
def prefixEnd_6827897 : Nat := 4983230072969 + 3 ^ 40 * 6827897 * 2
def baseEnd_6827897 : Nat := 3505993020391977555286579

theorem tailTrace_6827897 : CollatzResearch.WordTrace tailWord_6827897 prefixEnd_6827897 3505993020391977555286579 := by
  unfold tailWord_6827897
  simp only [CollatzResearch.WordTrace]
  refine ⟨249033862544702755813793945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166022575029801837209195963 249033862544702755813793945)
  ·
    refine ⟨186775396908527066860345459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249033862544702755813793945 186775396908527066860345459)
    ·
      refine ⟨280163095362790600290518189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186775396908527066860345459 280163095362790600290518189)
      ·
        refine ⟨105061160761046475108944321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280163095362790600290518189 105061160761046475108944321)
        ·
          refine ⟨78795870570784856331708241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105061160761046475108944321 78795870570784856331708241)
          ·
            refine ⟨59096902928088642248781181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78795870570784856331708241 59096902928088642248781181)
            ·
              refine ⟨22161338598033240843292943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59096902928088642248781181 22161338598033240843292943)
              ·
                refine ⟨33242007897049861264939415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22161338598033240843292943 33242007897049861264939415)
                ·
                  refine ⟨49863011845574791897409123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33242007897049861264939415 49863011845574791897409123)
                  ·
                    refine ⟨74794517768362187846113685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49863011845574791897409123 74794517768362187846113685)
                    ·
                      refine ⟨3505993020391977555286579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74794517768362187846113685 3505993020391977555286579)
                      ·
                        rfl

theorem cell23_6827897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_6827897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827897 prefixEnd_6827897 := by exact prefixLift 6827897
  have htrace : WordTrace (prefixWord ++ tailWord_6827897) baseStart_6827897 baseEnd_6827897 := by
    simpa [prefixWord, tailWord_6827897, baseEnd_6827897] using wordTrace_append hprefix tailTrace_6827897
  have hstable : (prefixWord ++ tailWord_6827897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827897).length < 2 ^ (prefixWord ++ tailWord_6827897).sum := by decide
  have hdescent : baseEnd_6827897 < baseStart_6827897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827907 : List Nat := [1, 1, 1, 3, 4, 3, 1, 9]
def baseStart_6827907 : Nat := 118140960795 + 6827907 * 2 ^ 59
def prefixEnd_6827907 : Nat := 4983230072969 + 3 ^ 40 * 6827907 * 2
def baseEnd_6827907 : Nat := 129851783525871204302279

theorem tailTrace_6827907 : CollatzResearch.WordTrace tailWord_6827907 prefixEnd_6827907 129851783525871204302279 := by
  unfold tailWord_6827907
  simp only [CollatzResearch.WordTrace]
  refine ⟨249034227274666527521657975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166022818183111018347771983 249034227274666527521657975)
  ·
    refine ⟨373551340911999791282486963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249034227274666527521657975 373551340911999791282486963)
    ·
      refine ⟨560327011367999686923730445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373551340911999791282486963 560327011367999686923730445)
      ·
        refine ⟨210122629262999882596398917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 560327011367999686923730445 210122629262999882596398917)
        ·
          refine ⟨39397992986812477986824797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210122629262999882596398917 39397992986812477986824797)
          ·
            refine ⟨14774247370054679245059299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39397992986812477986824797 14774247370054679245059299)
            ·
              refine ⟨22161371055082018867588949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14774247370054679245059299 22161371055082018867588949)
              ·
                refine ⟨129851783525871204302279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22161371055082018867588949 129851783525871204302279)
                ·
                  rfl

theorem cell23_6827907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 9].length) (baseStart_6827907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827907 prefixEnd_6827907 := by exact prefixLift 6827907
  have htrace : WordTrace (prefixWord ++ tailWord_6827907) baseStart_6827907 baseEnd_6827907 := by
    simpa [prefixWord, tailWord_6827907, baseEnd_6827907] using wordTrace_append hprefix tailTrace_6827907
  have hstable : (prefixWord ++ tailWord_6827907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827907).length < 2 ^ (prefixWord ++ tailWord_6827907).sum := by decide
  have hdescent : baseEnd_6827907 < baseStart_6827907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827912 : List Nat := [2, 1, 3, 3, 4, 1, 1, 3, 1, 1, 3]
def baseStart_6827912 : Nat := 118140960795 + 6827912 * 2 ^ 59
def prefixEnd_6827912 : Nat := 4983230072969 + 3 ^ 40 * 6827912 * 2
def baseEnd_6827912 : Nat := 3506000722601794996599011

theorem tailTrace_6827912 : CollatzResearch.WordTrace tailWord_6827912 prefixEnd_6827912 3506000722601794996599011 := by
  unfold tailWord_6827912
  simp only [CollatzResearch.WordTrace]
  refine ⟨124517204819824206687794995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166022939759765608917059993 124517204819824206687794995)
  ·
    refine ⟨186775807229736310031692493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124517204819824206687794995 186775807229736310031692493)
    ·
      refine ⟨70040927711151116261884685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186775807229736310031692493 70040927711151116261884685)
      ·
        refine ⟨26265347891681668598206757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70040927711151116261884685 26265347891681668598206757)
        ·
          refine ⟨4924752729690312862163767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26265347891681668598206757 4924752729690312862163767)
          ·
            refine ⟨7387129094535469293245651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4924752729690312862163767 7387129094535469293245651)
            ·
              refine ⟨11080693641803203939868477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7387129094535469293245651 11080693641803203939868477)
              ·
                refine ⟨4155260115676201477450679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11080693641803203939868477 4155260115676201477450679)
                ·
                  refine ⟨6232890173514302216176019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4155260115676201477450679 6232890173514302216176019)
                  ·
                    refine ⟨9349335260271453324264029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6232890173514302216176019 9349335260271453324264029)
                    ·
                      refine ⟨3506000722601794996599011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9349335260271453324264029 3506000722601794996599011)
                      ·
                        rfl

theorem cell23_6827912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_6827912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827912 prefixEnd_6827912 := by exact prefixLift 6827912
  have htrace : WordTrace (prefixWord ++ tailWord_6827912) baseStart_6827912 baseEnd_6827912 := by
    simpa [prefixWord, tailWord_6827912, baseEnd_6827912] using wordTrace_append hprefix tailTrace_6827912
  have hstable : (prefixWord ++ tailWord_6827912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827912).length < 2 ^ (prefixWord ++ tailWord_6827912).sum := by decide
  have hdescent : baseEnd_6827912 < baseStart_6827912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827924 : List Nat := [2, 4, 2, 1, 1, 4, 9]
def baseStart_6827924 : Nat := 118140960795 + 6827924 * 2 ^ 59
def prefixEnd_6827924 : Nat := 4983230072969 + 3 ^ 40 * 6827924 * 2
def baseEnd_6827924 : Nat := 43284035609501838884555

theorem tailTrace_6827924 : CollatzResearch.WordTrace tailWord_6827924 prefixEnd_6827924 43284035609501838884555 := by
  unfold tailWord_6827924
  simp only [CollatzResearch.WordTrace]
  refine ⟨124517423657802469712513413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166023231543736626283351217 124517423657802469712513413)
  ·
    refine ⟨23347016935837963071096265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124517423657802469712513413 23347016935837963071096265)
    ·
      refine ⟨17510262701878472303322199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23347016935837963071096265 17510262701878472303322199)
      ·
        refine ⟨26265394052817708454983299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17510262701878472303322199 26265394052817708454983299)
        ·
          refine ⟨39398091079226562682474949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26265394052817708454983299 39398091079226562682474949)
          ·
            refine ⟨7387142077354980502964053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39398091079226562682474949 7387142077354980502964053)
            ·
              refine ⟨43284035609501838884555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7387142077354980502964053 43284035609501838884555)
              ·
                rfl

theorem cell23_6827924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 9].length) (baseStart_6827924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827924 prefixEnd_6827924 := by exact prefixLift 6827924
  have htrace : WordTrace (prefixWord ++ tailWord_6827924) baseStart_6827924 baseEnd_6827924 := by
    simpa [prefixWord, tailWord_6827924, baseEnd_6827924] using wordTrace_append hprefix tailTrace_6827924
  have hstable : (prefixWord ++ tailWord_6827924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827924).length < 2 ^ (prefixWord ++ tailWord_6827924).sum := by decide
  have hdescent : baseEnd_6827924 < baseStart_6827924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827935 : List Nat := [1, 1, 2, 5, 3, 2, 1, 1, 3, 2, 2]
def baseStart_6827935 : Nat := 118140960795 + 6827935 * 2 ^ 59
def prefixEnd_6827935 : Nat := 4983230072969 + 3 ^ 40 * 6827935 * 2
def baseEnd_6827935 : Nat := 3506012532656848406611405

theorem tailTrace_6827935 : CollatzResearch.WordTrace tailWord_6827935 prefixEnd_6827935 3506012532656848406611405 := by
  unfold tailWord_6827935
  simp only [CollatzResearch.WordTrace]
  refine ⟨249035248518565088303677259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166023499012376725535784839 249035248518565088303677259)
  ·
    refine ⟨373552872777847632455515889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249035248518565088303677259 373552872777847632455515889)
    ·
      refine ⟨280164654583385724341636917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373552872777847632455515889 280164654583385724341636917)
      ·
        refine ⟨26265436367192411657028461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 280164654583385724341636917 26265436367192411657028461)
        ·
          refine ⟨9849538637697154371385673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26265436367192411657028461 9849538637697154371385673)
          ·
            refine ⟨7387153978272865778539255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9849538637697154371385673 7387153978272865778539255)
            ·
              refine ⟨11080730967409298667808883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7387153978272865778539255 11080730967409298667808883)
              ·
                refine ⟨16621096451113948001713325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11080730967409298667808883 16621096451113948001713325)
                ·
                  refine ⟨6232911169167730500642497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16621096451113948001713325 6232911169167730500642497)
                  ·
                    refine ⟨4674683376875797875481873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6232911169167730500642497 4674683376875797875481873)
                    ·
                      refine ⟨3506012532656848406611405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4674683376875797875481873 3506012532656848406611405)
                      ·
                        rfl

theorem cell23_6827935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_6827935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827935 prefixEnd_6827935 := by exact prefixLift 6827935
  have htrace : WordTrace (prefixWord ++ tailWord_6827935) baseStart_6827935 baseEnd_6827935 := by
    simpa [prefixWord, tailWord_6827935, baseEnd_6827935] using wordTrace_append hprefix tailTrace_6827935
  have hstable : (prefixWord ++ tailWord_6827935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827935).length < 2 ^ (prefixWord ++ tailWord_6827935).sum := by decide
  have hdescent : baseEnd_6827935 < baseStart_6827935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827951 : List Nat := [1, 1, 2, 1, 2, 2, 5, 3, 2, 1, 3]
def baseStart_6827951 : Nat := 118140960795 + 6827951 * 2 ^ 59
def prefixEnd_6827951 : Nat := 4983230072969 + 3 ^ 40 * 6827951 * 2
def baseEnd_6827951 : Nat := 3506020748347320344011331

theorem tailTrace_6827951 : CollatzResearch.WordTrace tailWord_6827951 prefixEnd_6827951 3506020748347320344011331 := by
  unfold tailWord_6827951
  simp only [CollatzResearch.WordTrace]
  refine ⟨249035832086507123036259707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166023888057671415357506471 249035832086507123036259707)
  ·
    refine ⟨373553748129760684554389561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249035832086507123036259707 373553748129760684554389561)
    ·
      refine ⟨280165311097320513415792171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373553748129760684554389561 280165311097320513415792171)
      ·
        refine ⟨420247966645980770123688257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280165311097320513415792171 420247966645980770123688257)
        ·
          refine ⟨315185974984485577592766193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420247966645980770123688257 315185974984485577592766193)
          ·
            refine ⟨236389481238364183194574645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315185974984485577592766193 236389481238364183194574645)
            ·
              refine ⟨22161513866096642174491373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 236389481238364183194574645 22161513866096642174491373)
              ·
                refine ⟨8310567699786240815434265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22161513866096642174491373 8310567699786240815434265)
                ·
                  refine ⟨6232925774839680611575699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8310567699786240815434265 6232925774839680611575699)
                  ·
                    refine ⟨9349388662259520917363549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6232925774839680611575699 9349388662259520917363549)
                    ·
                      refine ⟨3506020748347320344011331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9349388662259520917363549 3506020748347320344011331)
                      ·
                        rfl

theorem cell23_6827951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 2, 1, 3].length) (baseStart_6827951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827951 prefixEnd_6827951 := by exact prefixLift 6827951
  have htrace : WordTrace (prefixWord ++ tailWord_6827951) baseStart_6827951 baseEnd_6827951 := by
    simpa [prefixWord, tailWord_6827951, baseEnd_6827951] using wordTrace_append hprefix tailTrace_6827951
  have hstable : (prefixWord ++ tailWord_6827951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827951).length < 2 ^ (prefixWord ++ tailWord_6827951).sum := by decide
  have hdescent : baseEnd_6827951 < baseStart_6827951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827961 : List Nat := [1, 2, 1, 4, 2, 1, 3, 1, 3, 3, 2]
def baseStart_6827961 : Nat := 118140960795 + 6827961 * 2 ^ 59
def prefixEnd_6827961 : Nat := 4983230072969 + 3 ^ 40 * 6827961 * 2
def baseEnd_6827961 : Nat := 3506025883153865304886285

theorem tailTrace_6827961 : CollatzResearch.WordTrace tailWord_6827961 prefixEnd_6827961 3506025883153865304886285 := by
  unfold tailWord_6827961
  simp only [CollatzResearch.WordTrace]
  refine ⟨249036196816470894744123737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166024131210980596496082491 249036196816470894744123737)
  ·
    refine ⟨186777147612353171058092803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249036196816470894744123737 186777147612353171058092803)
    ·
      refine ⟨280165721418529756587139205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186777147612353171058092803 280165721418529756587139205)
      ·
        refine ⟨52531072765974329360088601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 280165721418529756587139205 52531072765974329360088601)
        ·
          refine ⟨39398304574480747020066451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52531072765974329360088601 39398304574480747020066451)
          ·
            refine ⟨59097456861721120530099677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39398304574480747020066451 59097456861721120530099677)
            ·
              refine ⟨22161546323145420198787379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59097456861721120530099677 22161546323145420198787379)
              ·
                refine ⟨33242319484718130298181069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22161546323145420198787379 33242319484718130298181069)
                ·
                  refine ⟨12465869806769298861817901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33242319484718130298181069 12465869806769298861817901)
                  ·
                    refine ⟨4674701177538487073181713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12465869806769298861817901 4674701177538487073181713)
                    ·
                      refine ⟨3506025883153865304886285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4674701177538487073181713 3506025883153865304886285)
                      ·
                        rfl

theorem cell23_6827961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_6827961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827961 prefixEnd_6827961 := by exact prefixLift 6827961
  have htrace : WordTrace (prefixWord ++ tailWord_6827961) baseStart_6827961 baseEnd_6827961 := by
    simpa [prefixWord, tailWord_6827961, baseEnd_6827961] using wordTrace_append hprefix tailTrace_6827961
  have hstable : (prefixWord ++ tailWord_6827961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827961).length < 2 ^ (prefixWord ++ tailWord_6827961).sum := by decide
  have hdescent : baseEnd_6827961 < baseStart_6827961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6827986 : List Nat := [3, 2, 2, 3, 3, 1, 2, 2, 1, 2, 2]
def baseStart_6827986 : Nat := 118140960795 + 6827986 * 2 ^ 59
def prefixEnd_6827986 : Nat := 4983230072969 + 3 ^ 40 * 6827986 * 2
def baseEnd_6827986 : Nat := 3506038720170227707073671

theorem tailTrace_6827986 : CollatzResearch.WordTrace tailWord_6827986 prefixEnd_6827986 3506038720170227707073671 := by
  unfold tailWord_6827986
  simp only [CollatzResearch.WordTrace]
  refine ⟨62259277160345081003445953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166024739094253549342522541 62259277160345081003445953)
  ·
    refine ⟨46694457870258810752584465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62259277160345081003445953 46694457870258810752584465)
    ·
      refine ⟨35020843402694108064438349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46694457870258810752584465 35020843402694108064438349)
      ·
        refine ⟨13132816276010290524164381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35020843402694108064438349 13132816276010290524164381)
        ·
          refine ⟨4924806103503858946561643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13132816276010290524164381 4924806103503858946561643)
          ·
            refine ⟨7387209155255788419842465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4924806103503858946561643 7387209155255788419842465)
            ·
              refine ⟨5540406866441841314881849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7387209155255788419842465 5540406866441841314881849)
              ·
                refine ⟨4155305149831380986161387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5540406866441841314881849 4155305149831380986161387)
                ·
                  refine ⟨6232957724747071479242081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4155305149831380986161387 6232957724747071479242081)
                  ·
                    refine ⟨4674718293560303609431561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6232957724747071479242081 4674718293560303609431561)
                    ·
                      refine ⟨3506038720170227707073671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4674718293560303609431561 3506038720170227707073671)
                      ·
                        rfl

theorem cell23_6827986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_6827986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6827986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6827986 prefixEnd_6827986 := by exact prefixLift 6827986
  have htrace : WordTrace (prefixWord ++ tailWord_6827986) baseStart_6827986 baseEnd_6827986 := by
    simpa [prefixWord, tailWord_6827986, baseEnd_6827986] using wordTrace_append hprefix tailTrace_6827986
  have hstable : (prefixWord ++ tailWord_6827986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6827986).length < 2 ^ (prefixWord ++ tailWord_6827986).sum := by decide
  have hdescent : baseEnd_6827986 < baseStart_6827986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6827986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828004 : List Nat := [2, 3, 1, 1, 1, 1, 5, 1, 2, 2, 4]
def baseStart_6828004 : Nat := 118140960795 + 6828004 * 2 ^ 59
def prefixEnd_6828004 : Nat := 4983230072969 + 3 ^ 40 * 6828004 * 2
def baseEnd_6828004 : Nat := 3506047962822008636648587

theorem tailTrace_6828004 : CollatzResearch.WordTrace tailWord_6828004 prefixEnd_6828004 3506047962822008636648587 := by
  unfold tailWord_6828004
  simp only [CollatzResearch.WordTrace]
  refine ⟨124518882577657556543969533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166025176770210075391959377 124518882577657556543969533)
  ·
    refine ⟨46694580966621583703988575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124518882577657556543969533 46694580966621583703988575)
    ·
      refine ⟨70041871449932375555982863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46694580966621583703988575 70041871449932375555982863)
      ·
        refine ⟨105062807174898563333974295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70041871449932375555982863 105062807174898563333974295)
        ·
          refine ⟨157594210762347845000961443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105062807174898563333974295 157594210762347845000961443)
          ·
            refine ⟨236391316143521767501442165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157594210762347845000961443 236391316143521767501442165)
            ·
              refine ⟨22161685888455165703260203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 236391316143521767501442165 22161685888455165703260203)
              ·
                refine ⟨33242528832682748554890305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22161685888455165703260203 33242528832682748554890305)
                ·
                  refine ⟨24931896624512061416167729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33242528832682748554890305 24931896624512061416167729)
                  ·
                    refine ⟨18698922468384046062125797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24931896624512061416167729 18698922468384046062125797)
                    ·
                      refine ⟨3506047962822008636648587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18698922468384046062125797 3506047962822008636648587)
                      ·
                        rfl

theorem cell23_6828004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_6828004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828004 prefixEnd_6828004 := by exact prefixLift 6828004
  have htrace : WordTrace (prefixWord ++ tailWord_6828004) baseStart_6828004 baseEnd_6828004 := by
    simpa [prefixWord, tailWord_6828004, baseEnd_6828004] using wordTrace_append hprefix tailTrace_6828004
  have hstable : (prefixWord ++ tailWord_6828004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828004).length < 2 ^ (prefixWord ++ tailWord_6828004).sum := by decide
  have hdescent : baseEnd_6828004 < baseStart_6828004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828014 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 9]
def baseStart_6828014 : Nat := 118140960795 + 6828014 * 2 ^ 59
def prefixEnd_6828014 : Nat := 4983230072969 + 3 ^ 40 * 6828014 * 2
def baseEnd_6828014 : Nat := 389561455292061510835949

theorem tailTrace_6828014 : CollatzResearch.WordTrace tailWord_6828014 prefixEnd_6828014 389561455292061510835949 := by
  unfold tailWord_6828014
  simp only [CollatzResearch.WordTrace]
  refine ⟨31129766235659860599475387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166025419923519256530535397 31129766235659860599475387)
  ·
    refine ⟨46694649353489790899213081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31129766235659860599475387 46694649353489790899213081)
    ·
      refine ⟨35020987015117343174409811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46694649353489790899213081 35020987015117343174409811)
      ·
        refine ⟨52531480522676014761614717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35020987015117343174409811 52531480522676014761614717)
        ·
          refine ⟨19699305196003505535605519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52531480522676014761614717 19699305196003505535605519)
          ·
            refine ⟨29548957794005258303408279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19699305196003505535605519 29548957794005258303408279)
            ·
              refine ⟨44323436691007887455112419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29548957794005258303408279 44323436691007887455112419)
              ·
                refine ⟨66485155036511831182668629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44323436691007887455112419 66485155036511831182668629)
                ·
                  refine ⟨389561455292061510835949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66485155036511831182668629 389561455292061510835949)
                  ·
                    rfl

theorem cell23_6828014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 9].length) (baseStart_6828014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828014 prefixEnd_6828014 := by exact prefixLift 6828014
  have htrace : WordTrace (prefixWord ++ tailWord_6828014) baseStart_6828014 baseEnd_6828014 := by
    simpa [prefixWord, tailWord_6828014, baseEnd_6828014] using wordTrace_append hprefix tailTrace_6828014
  have hstable : (prefixWord ++ tailWord_6828014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828014).length < 2 ^ (prefixWord ++ tailWord_6828014).sum := by decide
  have hdescent : baseEnd_6828014 < baseStart_6828014 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828042 : List Nat := [3, 1, 2, 2, 4, 2, 1, 2, 2, 2, 2]
def baseStart_6828042 : Nat := 118140960795 + 6828042 * 2 ^ 59
def prefixEnd_6828042 : Nat := 4983230072969 + 3 ^ 40 * 6828042 * 2
def baseEnd_6828042 : Nat := 3506067475086879487973413

theorem tailTrace_6828042 : CollatzResearch.WordTrace tailWord_6828042 prefixEnd_6828042 3506067475086879487973413 := by
  unfold tailWord_6828042
  simp only [CollatzResearch.WordTrace]
  refine ⟨62259787782294361394455595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166026100752784963718548253 62259787782294361394455595)
  ·
    refine ⟨93389681673441542091683393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62259787782294361394455595 93389681673441542091683393)
    ·
      refine ⟨70042261255081156568762545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93389681673441542091683393 70042261255081156568762545)
      ·
        refine ⟨52531695941310867426571909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70042261255081156568762545 52531695941310867426571909)
        ·
          refine ⟨9849692988995787642482233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52531695941310867426571909 9849692988995787642482233)
          ·
            refine ⟨7387269741746840731861675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9849692988995787642482233 7387269741746840731861675)
            ·
              refine ⟨11080904612620261097792513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7387269741746840731861675 11080904612620261097792513)
              ·
                refine ⟨8310678459465195823344385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11080904612620261097792513 8310678459465195823344385)
                ·
                  refine ⟨6233008844598896867508289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8310678459465195823344385 6233008844598896867508289)
                  ·
                    refine ⟨4674756633449172650631217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6233008844598896867508289 4674756633449172650631217)
                    ·
                      refine ⟨3506067475086879487973413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4674756633449172650631217 3506067475086879487973413)
                      ·
                        rfl

theorem cell23_6828042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_6828042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828042 prefixEnd_6828042 := by exact prefixLift 6828042
  have htrace : WordTrace (prefixWord ++ tailWord_6828042) baseStart_6828042 baseEnd_6828042 := by
    simpa [prefixWord, tailWord_6828042, baseEnd_6828042] using wordTrace_append hprefix tailTrace_6828042
  have hstable : (prefixWord ++ tailWord_6828042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828042).length < 2 ^ (prefixWord ++ tailWord_6828042).sum := by decide
  have hdescent : baseEnd_6828042 < baseStart_6828042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828044 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 4, 5]
def baseStart_6828044 : Nat := 118140960795 + 6828044 * 2 ^ 59
def prefixEnd_6828044 : Nat := 4983230072969 + 3 ^ 40 * 6828044 * 2
def baseEnd_6828044 : Nat := 1168689500682729493382801

theorem tailTrace_6828044 : CollatzResearch.WordTrace tailWord_6828044 prefixEnd_6828044 1168689500682729493382801 := by
  unfold tailWord_6828044
  simp only [CollatzResearch.WordTrace]
  refine ⟨124519612037585099959697593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166026149383446799946263457 124519612037585099959697593)
  ·
    refine ⟨93389709028188824969773195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124519612037585099959697593 93389709028188824969773195)
    ·
      refine ⟨140084563542283237454659793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93389709028188824969773195 140084563542283237454659793)
      ·
        refine ⟨105063422656712428090994845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140084563542283237454659793 105063422656712428090994845)
        ·
          refine ⟨39398783496267160534123067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105063422656712428090994845 39398783496267160534123067)
          ·
            refine ⟨59098175244400740801184601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39398783496267160534123067 59098175244400740801184601)
            ·
              refine ⟨44323631433300555600888451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59098175244400740801184601 44323631433300555600888451)
              ·
                refine ⟨66485447149950833401332677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44323631433300555600888451 66485447149950833401332677)
                ·
                  refine ⟨12466021340615781262749877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66485447149950833401332677 12466021340615781262749877)
                  ·
                    refine ⟨1168689500682729493382801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12466021340615781262749877 1168689500682729493382801)
                    ·
                      rfl

theorem cell23_6828044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 4, 5].length) (baseStart_6828044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828044 prefixEnd_6828044 := by exact prefixLift 6828044
  have htrace : WordTrace (prefixWord ++ tailWord_6828044) baseStart_6828044 baseEnd_6828044 := by
    simpa [prefixWord, tailWord_6828044, baseEnd_6828044] using wordTrace_append hprefix tailTrace_6828044
  have hstable : (prefixWord ++ tailWord_6828044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828044).length < 2 ^ (prefixWord ++ tailWord_6828044).sum := by decide
  have hdescent : baseEnd_6828044 < baseStart_6828044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828047 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 8]
def baseStart_6828047 : Nat := 118140960795 + 6828047 * 2 ^ 59
def prefixEnd_6828047 : Nat := 4983230072969 + 3 ^ 40 * 6828047 * 2
def baseEnd_6828047 : Nat := 3506070042490151968410889

theorem tailTrace_6828047 : CollatzResearch.WordTrace tailWord_6828047 prefixEnd_6828047 3506070042490151968410889 := by
  unfold tailWord_6828047
  simp only [CollatzResearch.WordTrace]
  refine ⟨249039333494159331431754395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166026222329439554287836263 249039333494159331431754395)
  ·
    refine ⟨373559000241238997147631593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249039333494159331431754395 373559000241238997147631593)
    ·
      refine ⟨280169250180929247860723695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373559000241238997147631593 280169250180929247860723695)
      ·
        refine ⟨420253875271393871791085543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280169250180929247860723695 420253875271393871791085543)
        ·
          refine ⟨630380812907090807686628315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420253875271393871791085543 630380812907090807686628315)
          ·
            refine ⟨945571219360636211529942473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630380812907090807686628315 945571219360636211529942473)
            ·
              refine ⟨709178414520477158647456855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 945571219360636211529942473 709178414520477158647456855)
              ·
                refine ⟨1063767621780715737971185283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 709178414520477158647456855 1063767621780715737971185283)
                ·
                  refine ⟨1595651432671073606956777925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1063767621780715737971185283 1595651432671073606956777925)
                  ·
                    refine ⟨299184643625826301304395861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1595651432671073606956777925 299184643625826301304395861)
                    ·
                      refine ⟨3506070042490151968410889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 299184643625826301304395861 3506070042490151968410889)
                      ·
                        rfl

theorem cell23_6828047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 8].length) (baseStart_6828047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828047 prefixEnd_6828047 := by exact prefixLift 6828047
  have htrace : WordTrace (prefixWord ++ tailWord_6828047) baseStart_6828047 baseEnd_6828047 := by
    simpa [prefixWord, tailWord_6828047, baseEnd_6828047] using wordTrace_append hprefix tailTrace_6828047
  have hstable : (prefixWord ++ tailWord_6828047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828047).length < 2 ^ (prefixWord ++ tailWord_6828047).sum := by decide
  have hdescent : baseEnd_6828047 < baseStart_6828047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828108 : List Nat := [2, 2, 1, 3, 1, 1, 2, 6, 1, 4]
def baseStart_6828108 : Nat := 118140960795 + 6828108 * 2 ^ 59
def prefixEnd_6828108 : Nat := 4983230072969 + 3 ^ 40 * 6828108 * 2
def baseEnd_6828108 : Nat := 1168700454936692076582703

theorem tailTrace_6828108 : CollatzResearch.WordTrace tailWord_6828108 prefixEnd_6828108 1168700454936692076582703 := by
  unfold tailWord_6828108
  simp only [CollatzResearch.WordTrace]
  refine ⟨124520779173469169424862489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166027705564625559233149985 124520779173469169424862489)
  ·
    refine ⟨93390584380101877068646867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124520779173469169424862489 93390584380101877068646867)
    ·
      refine ⟨140085876570152815602970301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93390584380101877068646867 140085876570152815602970301)
      ·
        refine ⟨52532203713807305851113863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140085876570152815602970301 52532203713807305851113863)
        ·
          refine ⟨78798305570710958776670795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52532203713807305851113863 78798305570710958776670795)
          ·
            refine ⟨118197458356066438165006193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78798305570710958776670795 118197458356066438165006193)
            ·
              refine ⟨88648093767049828623754645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118197458356066438165006193 88648093767049828623754645)
              ·
                refine ⟨4155379395330460716738499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88648093767049828623754645 4155379395330460716738499)
                ·
                  refine ⟨6233069092995691075107749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4155379395330460716738499 6233069092995691075107749)
                  ·
                    refine ⟨1168700454936692076582703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6233069092995691075107749 1168700454936692076582703)
                    ·
                      rfl

theorem cell23_6828108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 6, 1, 4].length) (baseStart_6828108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828108 prefixEnd_6828108 := by exact prefixLift 6828108
  have htrace : WordTrace (prefixWord ++ tailWord_6828108) baseStart_6828108 baseEnd_6828108 := by
    simpa [prefixWord, tailWord_6828108, baseEnd_6828108] using wordTrace_append hprefix tailTrace_6828108
  have hstable : (prefixWord ++ tailWord_6828108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828108).length < 2 ^ (prefixWord ++ tailWord_6828108).sum := by decide
  have hdescent : baseEnd_6828108 < baseStart_6828108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828171 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 4, 6, 2]
def baseStart_6828171 : Nat := 118140960795 + 6828171 * 2 ^ 59
def prefixEnd_6828171 : Nat := 4983230072969 + 3 ^ 40 * 6828171 * 2
def baseEnd_6828171 : Nat := 3506133714091309483260319

theorem tailTrace_6828171 : CollatzResearch.WordTrace tailWord_6828171 prefixEnd_6828171 3506133714091309483260319 := by
  unfold tailWord_6828171
  simp only [CollatzResearch.WordTrace]
  refine ⟨249043856145710100609268367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166029237430473400406178911 249043856145710100609268367)
  ·
    refine ⟨373565784218565150913902551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249043856145710100609268367 373565784218565150913902551)
    ·
      refine ⟨560348676327847726370853827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373565784218565150913902551 560348676327847726370853827)
      ·
        refine ⟨840523014491771589556280741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560348676327847726370853827 840523014491771589556280741)
        ·
          refine ⟨157598065217207173041802639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 840523014491771589556280741 157598065217207173041802639)
          ·
            refine ⟨236397097825810759562703959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157598065217207173041802639 236397097825810759562703959)
            ·
              refine ⟨354595646738716139344055939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236397097825810759562703959 354595646738716139344055939)
              ·
                refine ⟨531893470108074209016083909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354595646738716139344055939 531893470108074209016083909)
                ·
                  refine ⟨99730025645263914190515733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 531893470108074209016083909 99730025645263914190515733)
                  ·
                    refine ⟨4674844952121745977680425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 99730025645263914190515733 4674844952121745977680425)
                    ·
                      refine ⟨3506133714091309483260319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4674844952121745977680425 3506133714091309483260319)
                      ·
                        rfl

theorem cell23_6828171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 6, 2].length) (baseStart_6828171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828171 prefixEnd_6828171 := by exact prefixLift 6828171
  have htrace : WordTrace (prefixWord ++ tailWord_6828171) baseStart_6828171 baseEnd_6828171 := by
    simpa [prefixWord, tailWord_6828171, baseEnd_6828171] using wordTrace_append hprefix tailTrace_6828171
  have hstable : (prefixWord ++ tailWord_6828171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828171).length < 2 ^ (prefixWord ++ tailWord_6828171).sum := by decide
  have hdescent : baseEnd_6828171 < baseStart_6828171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828181 : List Nat := [1, 3, 2, 1, 1, 1, 6, 1, 1, 6]
def baseStart_6828181 : Nat := 118140960795 + 6828181 * 2 ^ 59
def prefixEnd_6828181 : Nat := 4983230072969 + 3 ^ 40 * 6828181 * 2
def baseEnd_6828181 : Nat := 1168712949632618148045091

theorem tailTrace_6828181 : CollatzResearch.WordTrace tailWord_6828181 prefixEnd_6828181 1168712949632618148045091 := by
  unfold tailWord_6828181
  simp only [CollatzResearch.WordTrace]
  refine ⟨249044220875673872317132397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166029480583782581544754931 249044220875673872317132397)
  ·
    refine ⟨93391582828377702118924649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249044220875673872317132397 93391582828377702118924649)
    ·
      refine ⟨70043687121283276589193487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93391582828377702118924649 70043687121283276589193487)
      ·
        refine ⟨105065530681924914883790231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70043687121283276589193487 105065530681924914883790231)
        ·
          refine ⟨157598296022887372325685347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105065530681924914883790231 157598296022887372325685347)
          ·
            refine ⟨236397444034331058488528021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157598296022887372325685347 236397444034331058488528021)
            ·
              refine ⟨11081130189109268366649751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 236397444034331058488528021 11081130189109268366649751)
              ·
                refine ⟨16621695283663902549974627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11081130189109268366649751 16621695283663902549974627)
                ·
                  refine ⟨24932542925495853824961941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16621695283663902549974627 24932542925495853824961941)
                  ·
                    refine ⟨1168712949632618148045091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24932542925495853824961941 1168712949632618148045091)
                    ·
                      rfl

theorem cell23_6828181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_6828181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828181 prefixEnd_6828181 := by exact prefixLift 6828181
  have htrace : WordTrace (prefixWord ++ tailWord_6828181) baseStart_6828181 baseEnd_6828181 := by
    simpa [prefixWord, tailWord_6828181, baseEnd_6828181] using wordTrace_append hprefix tailTrace_6828181
  have hstable : (prefixWord ++ tailWord_6828181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828181).length < 2 ^ (prefixWord ++ tailWord_6828181).sum := by decide
  have hdescent : baseEnd_6828181 < baseStart_6828181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828188 : List Nat := [2, 2, 3, 2, 1, 1, 2, 4, 1, 1, 4]
def baseStart_6828188 : Nat := 118140960795 + 6828188 * 2 ^ 59
def prefixEnd_6828188 : Nat := 4983230072969 + 3 ^ 40 * 6828188 * 2
def baseEnd_6828188 : Nat := 3506142443262435916747741

theorem tailTrace_6828188 : CollatzResearch.WordTrace tailWord_6828188 prefixEnd_6828188 3506142443262435916747741 := by
  unfold tailWord_6828188
  simp only [CollatzResearch.WordTrace]
  refine ⟨124522238093324256256318609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166029650791099008341758145 124522238093324256256318609)
  ·
    refine ⟨93391678569993192192238957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124522238093324256256318609 93391678569993192192238957)
    ·
      refine ⟨35021879463747447072089609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93391678569993192192238957 35021879463747447072089609)
      ·
        refine ⟨26266409597810585304067207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35021879463747447072089609 26266409597810585304067207)
        ·
          refine ⟨39399614396715877956100811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26266409597810585304067207 39399614396715877956100811)
          ·
            refine ⟨59099421595073816934151217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39399614396715877956100811 59099421595073816934151217)
            ·
              refine ⟨44324566196305362700613413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59099421595073816934151217 44324566196305362700613413)
              ·
                refine ⟨8310856161807255506365015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44324566196305362700613413 8310856161807255506365015)
                ·
                  refine ⟨12466284242710883259547523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8310856161807255506365015 12466284242710883259547523)
                  ·
                    refine ⟨18699426364066324889321285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12466284242710883259547523 18699426364066324889321285)
                    ·
                      refine ⟨3506142443262435916747741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18699426364066324889321285 3506142443262435916747741)
                      ·
                        rfl

theorem cell23_6828188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_6828188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828188 prefixEnd_6828188 := by exact prefixLift 6828188
  have htrace : WordTrace (prefixWord ++ tailWord_6828188) baseStart_6828188 baseEnd_6828188 := by
    simpa [prefixWord, tailWord_6828188, baseEnd_6828188] using wordTrace_append hprefix tailTrace_6828188
  have hstable : (prefixWord ++ tailWord_6828188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828188).length < 2 ^ (prefixWord ++ tailWord_6828188).sum := by decide
  have hdescent : baseEnd_6828188 < baseStart_6828188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828199 : List Nat := [1, 1, 6, 2, 2, 1, 2, 3, 1, 1, 3]
def baseStart_6828199 : Nat := 118140960795 + 6828199 * 2 ^ 59
def prefixEnd_6828199 : Nat := 4983230072969 + 3 ^ 40 * 6828199 * 2
def baseEnd_6828199 : Nat := 3506148091549635373710191

theorem tailTrace_6828199 : CollatzResearch.WordTrace tailWord_6828199 prefixEnd_6828199 3506148091549635373710191 := by
  unfold tailWord_6828199
  simp only [CollatzResearch.WordTrace]
  refine ⟨249044877389608661391287651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166029918259739107594191767 249044877389608661391287651)
  ·
    refine ⟨373567316084412992086931477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249044877389608661391287651 373567316084412992086931477)
    ·
      refine ⟨17510967941456859004074913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 373567316084412992086931477 17510967941456859004074913)
      ·
        refine ⟨13133225956092644253056185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17510967941456859004074913 13133225956092644253056185)
        ·
          refine ⟨9849919467069483189792139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13133225956092644253056185 9849919467069483189792139)
          ·
            refine ⟨14774879200604224784688209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9849919467069483189792139 14774879200604224784688209)
            ·
              refine ⟨11081159400453168588516157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14774879200604224784688209 11081159400453168588516157)
              ·
                refine ⟨4155434775169938220693559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11081159400453168588516157 4155434775169938220693559)
                ·
                  refine ⟨6233152162754907331040339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4155434775169938220693559 6233152162754907331040339)
                  ·
                    refine ⟨9349728244132360996560509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6233152162754907331040339 9349728244132360996560509)
                    ·
                      refine ⟨3506148091549635373710191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9349728244132360996560509 3506148091549635373710191)
                      ·
                        rfl

theorem cell23_6828199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_6828199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828199 prefixEnd_6828199 := by exact prefixLift 6828199
  have htrace : WordTrace (prefixWord ++ tailWord_6828199) baseStart_6828199 baseEnd_6828199 := by
    simpa [prefixWord, tailWord_6828199, baseEnd_6828199] using wordTrace_append hprefix tailTrace_6828199
  have hstable : (prefixWord ++ tailWord_6828199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828199).length < 2 ^ (prefixWord ++ tailWord_6828199).sum := by decide
  have hdescent : baseEnd_6828199 < baseStart_6828199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828204 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 7]
def baseStart_6828204 : Nat := 118140960795 + 6828204 * 2 ^ 59
def prefixEnd_6828204 : Nat := 4983230072969 + 3 ^ 40 * 6828204 * 2
def baseEnd_6828204 : Nat := 3506150658952907854147667

theorem tailTrace_6828204 : CollatzResearch.WordTrace tailWord_6828204 prefixEnd_6828204 3506150658952907854147667 := by
  unfold tailWord_6828204
  simp only [CollatzResearch.WordTrace]
  refine ⟨124522529877295273622609833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166030039836393698163479777 124522529877295273622609833)
  ·
    refine ⟨93391897407971455216957375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124522529877295273622609833 93391897407971455216957375)
    ·
      refine ⟨140087846111957182825436063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93391897407971455216957375 140087846111957182825436063)
      ·
        refine ⟨210131769167935774238154095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140087846111957182825436063 210131769167935774238154095)
        ·
          refine ⟨315197653751903661357231143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210131769167935774238154095 315197653751903661357231143)
          ·
            refine ⟨472796480627855492035846715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315197653751903661357231143 472796480627855492035846715)
            ·
              refine ⟨709194720941783238053770073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472796480627855492035846715 709194720941783238053770073)
              ·
                refine ⟨531896040706337428540327555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 709194720941783238053770073 531896040706337428540327555)
                ·
                  refine ⟨797844061059506142810491333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 531896040706337428540327555 797844061059506142810491333)
                  ·
                    refine ⟨149595761448657401776967125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 797844061059506142810491333 149595761448657401776967125)
                    ·
                      refine ⟨3506150658952907854147667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149595761448657401776967125 3506150658952907854147667)
                      ·
                        rfl

theorem cell23_6828204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_6828204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828204 prefixEnd_6828204 := by exact prefixLift 6828204
  have htrace : WordTrace (prefixWord ++ tailWord_6828204) baseStart_6828204 baseEnd_6828204 := by
    simpa [prefixWord, tailWord_6828204, baseEnd_6828204] using wordTrace_append hprefix tailTrace_6828204
  have hstable : (prefixWord ++ tailWord_6828204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828204).length < 2 ^ (prefixWord ++ tailWord_6828204).sum := by decide
  have hdescent : baseEnd_6828204 < baseStart_6828204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828205 : List Nat := [1, 5, 2, 1, 2, 2, 1, 3, 1, 1, 4]
def baseStart_6828205 : Nat := 118140960795 + 6828205 * 2 ^ 59
def prefixEnd_6828205 : Nat := 4983230072969 + 3 ^ 40 * 6828205 * 2
def baseEnd_6828205 : Nat := 3506151172433562350235163

theorem tailTrace_6828205 : CollatzResearch.WordTrace tailWord_6828205 prefixEnd_6828205 3506151172433562350235163 := by
  unfold tailWord_6828205
  simp only [CollatzResearch.WordTrace]
  refine ⟨249045096227586924416006069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166030064151724616277337379 249045096227586924416006069)
  ·
    refine ⟨23347977771336274164000569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 249045096227586924416006069 23347977771336274164000569)
    ·
      refine ⟨17510983328502205623000427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23347977771336274164000569 17510983328502205623000427)
      ·
        refine ⟨26266474992753308434500641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17510983328502205623000427 26266474992753308434500641)
        ·
          refine ⟨19699856244564981325875481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26266474992753308434500641 19699856244564981325875481)
          ·
            refine ⟨14774892183423735994406611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19699856244564981325875481 14774892183423735994406611)
            ·
              refine ⟨22162338275135603991609917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14774892183423735994406611 22162338275135603991609917)
              ·
                refine ⟨8310876853175851496853719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22162338275135603991609917 8310876853175851496853719)
                ·
                  refine ⟨12466315279763777245280579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8310876853175851496853719 12466315279763777245280579)
                  ·
                    refine ⟨18699472919645665867920869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12466315279763777245280579 18699472919645665867920869)
                    ·
                      refine ⟨3506151172433562350235163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18699472919645665867920869 3506151172433562350235163)
                      ·
                        rfl

theorem cell23_6828205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_6828205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828205 prefixEnd_6828205 := by exact prefixLift 6828205
  have htrace : WordTrace (prefixWord ++ tailWord_6828205) baseStart_6828205 baseEnd_6828205 := by
    simpa [prefixWord, tailWord_6828205, baseEnd_6828205] using wordTrace_append hprefix tailTrace_6828205
  have hstable : (prefixWord ++ tailWord_6828205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828205).length < 2 ^ (prefixWord ++ tailWord_6828205).sum := by decide
  have hdescent : baseEnd_6828205 < baseStart_6828205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828215 : List Nat := [1, 1, 3, 1, 4, 4, 1, 2, 2, 4]
def baseStart_6828215 : Nat := 118140960795 + 6828215 * 2 ^ 59
def prefixEnd_6828215 : Nat := 4983230072969 + 3 ^ 40 * 6828215 * 2
def baseEnd_6828215 : Nat := 1168718769080035770370039

theorem tailTrace_6828215 : CollatzResearch.WordTrace tailWord_6828215 prefixEnd_6828215 1168718769080035770370039 := by
  unfold tailWord_6828215
  simp only [CollatzResearch.WordTrace]
  refine ⟨249045460957550696123870099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166030307305033797415913399 249045460957550696123870099)
  ·
    refine ⟨373568191436326044185805149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249045460957550696123870099 373568191436326044185805149)
    ·
      refine ⟨140088071788622266569676931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373568191436326044185805149 140088071788622266569676931)
      ·
        refine ⟨210132107682933399854515397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140088071788622266569676931 210132107682933399854515397)
        ·
          refine ⟨39399770190550012472721637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210132107682933399854515397 39399770190550012472721637)
          ·
            refine ⟨7387456910728127338635307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39399770190550012472721637 7387456910728127338635307)
            ·
              refine ⟨11081185366092191007952961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7387456910728127338635307 11081185366092191007952961)
              ·
                refine ⟨8310889024569143255964721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11081185366092191007952961 8310889024569143255964721)
                ·
                  refine ⟨6233166768426857441973541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8310889024569143255964721 6233166768426857441973541)
                  ·
                    refine ⟨1168718769080035770370039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6233166768426857441973541 1168718769080035770370039)
                    ·
                      rfl

theorem cell23_6828215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 2, 4].length) (baseStart_6828215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828215 prefixEnd_6828215 := by exact prefixLift 6828215
  have htrace : WordTrace (prefixWord ++ tailWord_6828215) baseStart_6828215 baseEnd_6828215 := by
    simpa [prefixWord, tailWord_6828215, baseEnd_6828215] using wordTrace_append hprefix tailTrace_6828215
  have hstable : (prefixWord ++ tailWord_6828215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828215).length < 2 ^ (prefixWord ++ tailWord_6828215).sum := by decide
  have hdescent : baseEnd_6828215 < baseStart_6828215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828225 : List Nat := [1, 2, 6, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_6828225 : Nat := 118140960795 + 6828225 * 2 ^ 59
def prefixEnd_6828225 : Nat := 4983230072969 + 3 ^ 40 * 6828225 * 2
def baseEnd_6828225 : Nat := 3506161442046652271985071

theorem tailTrace_6828225 : CollatzResearch.WordTrace tailWord_6828225 prefixEnd_6828225 3506161442046652271985071 := by
  unfold tailWord_6828225
  simp only [CollatzResearch.WordTrace]
  refine ⟨249045825687514467831734129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166030550458342978554489419 249045825687514467831734129)
  ·
    refine ⟨186784369265635850873800597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249045825687514467831734129 186784369265635850873800597)
    ·
      refine ⟨8755517309326680509709403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 186784369265635850873800597 8755517309326680509709403)
      ·
        refine ⟨13133275963990020764564105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8755517309326680509709403 13133275963990020764564105)
        ·
          refine ⟨9849956972992515573423079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13133275963990020764564105 9849956972992515573423079)
          ·
            refine ⟨14774935459488773360134619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9849956972992515573423079 14774935459488773360134619)
            ·
              refine ⟨22162403189233160040201929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14774935459488773360134619 22162403189233160040201929)
              ·
                refine ⟨16621802391924870030151447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22162403189233160040201929 16621802391924870030151447)
                ·
                  refine ⟨24932703587887305045227171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16621802391924870030151447 24932703587887305045227171)
                  ·
                    refine ⟨37399055381830957567840757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24932703587887305045227171 37399055381830957567840757)
                    ·
                      refine ⟨3506161442046652271985071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37399055381830957567840757 3506161442046652271985071)
                      ·
                        rfl

theorem cell23_6828225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_6828225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828225 prefixEnd_6828225 := by exact prefixLift 6828225
  have htrace : WordTrace (prefixWord ++ tailWord_6828225) baseStart_6828225 baseEnd_6828225 := by
    simpa [prefixWord, tailWord_6828225, baseEnd_6828225] using wordTrace_append hprefix tailTrace_6828225
  have hstable : (prefixWord ++ tailWord_6828225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828225).length < 2 ^ (prefixWord ++ tailWord_6828225).sum := by decide
  have hdescent : baseEnd_6828225 < baseStart_6828225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828245 : List Nat := [1, 3, 2, 4, 2, 2, 2, 7]
def baseStart_6828245 : Nat := 118140960795 + 6828245 * 2 ^ 59
def prefixEnd_6828245 : Nat := 4983230072969 + 3 ^ 40 * 6828245 * 2
def baseEnd_6828245 : Nat := 129858211542953414582777

theorem tailTrace_6828245 : CollatzResearch.WordTrace tailWord_6828245 prefixEnd_6828245 129858211542953414582777 := by
  unfold tailWord_6828245
  simp only [CollatzResearch.WordTrace]
  refine ⟨249046555147442011247462189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166031036764961340831641459 249046555147442011247462189)
  ·
    refine ⟨93392458180290754217798321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249046555147442011247462189 93392458180290754217798321)
    ·
      refine ⟨70044343635218065663348741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93392458180290754217798321 70044343635218065663348741)
      ·
        refine ⟨13133314431603387311877889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70044343635218065663348741 13133314431603387311877889)
        ·
          refine ⟨9849985823702540483908417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13133314431603387311877889 9849985823702540483908417)
          ·
            refine ⟨7387489367776905362931313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9849985823702540483908417 7387489367776905362931313)
            ·
              refine ⟨5540617025832679022198485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7387489367776905362931313 5540617025832679022198485)
              ·
                refine ⟨129858211542953414582777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5540617025832679022198485 129858211542953414582777)
                ·
                  rfl

theorem cell23_6828245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 7].length) (baseStart_6828245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828245 prefixEnd_6828245 := by exact prefixLift 6828245
  have htrace : WordTrace (prefixWord ++ tailWord_6828245) baseStart_6828245 baseEnd_6828245 := by
    simpa [prefixWord, tailWord_6828245, baseEnd_6828245] using wordTrace_append hprefix tailTrace_6828245
  have hstable : (prefixWord ++ tailWord_6828245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828245).length < 2 ^ (prefixWord ++ tailWord_6828245).sum := by decide
  have hdescent : baseEnd_6828245 < baseStart_6828245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828291 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 4]
def baseStart_6828291 : Nat := 118140960795 + 6828291 * 2 ^ 59
def prefixEnd_6828291 : Nat := 4983230072969 + 3 ^ 40 * 6828291 * 2
def baseEnd_6828291 : Nat := 3506195331769849013759767

theorem tailTrace_6828291 : CollatzResearch.WordTrace tailWord_6828291 prefixEnd_6828291 3506195331769849013759767 := by
  unfold tailWord_6828291
  simp only [CollatzResearch.WordTrace]
  refine ⟨249048232905275361103636727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166032155270183574069091151 249048232905275361103636727)
  ·
    refine ⟨373572349357913041655455091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249048232905275361103636727 373572349357913041655455091)
    ·
      refine ⟨560358524036869562483182637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373572349357913041655455091 560358524036869562483182637)
      ·
        refine ⟨210134446513826085931193489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 560358524036869562483182637 210134446513826085931193489)
        ·
          refine ⟨157600834885369564448395117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210134446513826085931193489 157600834885369564448395117)
          ·
            refine ⟨59100313082013586668148169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157600834885369564448395117 59100313082013586668148169)
            ·
              refine ⟨44325234811510190001111127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59100313082013586668148169 44325234811510190001111127)
              ·
                refine ⟨66487852217265285001666691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44325234811510190001111127 66487852217265285001666691)
                ·
                  refine ⟨99731778325897927502500037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66487852217265285001666691 99731778325897927502500037)
                  ·
                    refine ⟨18699708436105861406718757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99731778325897927502500037 18699708436105861406718757)
                    ·
                      refine ⟨3506195331769849013759767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18699708436105861406718757 3506195331769849013759767)
                      ·
                        rfl

theorem cell23_6828291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_6828291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828291 prefixEnd_6828291 := by exact prefixLift 6828291
  have htrace : WordTrace (prefixWord ++ tailWord_6828291) baseStart_6828291 baseEnd_6828291 := by
    simpa [prefixWord, tailWord_6828291, baseEnd_6828291] using wordTrace_append hprefix tailTrace_6828291
  have hstable : (prefixWord ++ tailWord_6828291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828291).length < 2 ^ (prefixWord ++ tailWord_6828291).sum := by decide
  have hdescent : baseEnd_6828291 < baseStart_6828291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828335 : List Nat := [1, 1, 2, 1, 2, 1, 8, 2, 5]
def baseStart_6828335 : Nat := 118140960795 + 6828335 * 2 ^ 59
def prefixEnd_6828335 : Nat := 4983230072969 + 3 ^ 40 * 6828335 * 2
def baseEnd_6828335 : Nat := 389579769435405204623285

theorem tailTrace_6828335 : CollatzResearch.WordTrace tailWord_6828335 prefixEnd_6828335 389579769435405204623285 := by
  unfold tailWord_6828335
  simp only [CollatzResearch.WordTrace]
  refine ⟨249049837717115956618238459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166033225144743971078825639 249049837717115956618238459)
  ·
    refine ⟨373574756575673934927357689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249049837717115956618238459 373574756575673934927357689)
    ·
      refine ⟨280181067431755451195518267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373574756575673934927357689 280181067431755451195518267)
      ·
        refine ⟨420271601147633176793277401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280181067431755451195518267 420271601147633176793277401)
        ·
          refine ⟨315203700860724882594958051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420271601147633176793277401 315203700860724882594958051)
          ·
            refine ⟨472805551291087323892437077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315203700860724882594958051 472805551291087323892437077)
            ·
              refine ⟨5540690054192429576864497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 472805551291087323892437077 5540690054192429576864497)
              ·
                refine ⟨4155517540644322182648373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5540690054192429576864497 4155517540644322182648373)
                ·
                  refine ⟨389579769435405204623285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4155517540644322182648373 389579769435405204623285)
                  ·
                    rfl

theorem cell23_6828335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 2, 5].length) (baseStart_6828335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828335 prefixEnd_6828335 := by exact prefixLift 6828335
  have htrace : WordTrace (prefixWord ++ tailWord_6828335) baseStart_6828335 baseEnd_6828335 := by
    simpa [prefixWord, tailWord_6828335, baseEnd_6828335] using wordTrace_append hprefix tailTrace_6828335
  have hstable : (prefixWord ++ tailWord_6828335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828335).length < 2 ^ (prefixWord ++ tailWord_6828335).sum := by decide
  have hdescent : baseEnd_6828335 < baseStart_6828335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828345 : List Nat := [1, 2, 1, 6, 1, 2, 1, 1, 2, 3, 3]
def baseStart_6828345 : Nat := 118140960795 + 6828345 * 2 ^ 59
def prefixEnd_6828345 : Nat := 4983230072969 + 3 ^ 40 * 6828345 * 2
def baseEnd_6828345 : Nat := 3506223059725191802484519

theorem tailTrace_6828345 : CollatzResearch.WordTrace tailWord_6828345 prefixEnd_6828345 3506223059725191802484519 := by
  unfold tailWord_6828345
  simp only [CollatzResearch.WordTrace]
  refine ⟨249050202447079728326102489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166033468298053152217401659 249050202447079728326102489)
  ·
    refine ⟨186787651835309796244576867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249050202447079728326102489 186787651835309796244576867)
    ·
      refine ⟨280181477752964694366865301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186787651835309796244576867 280181477752964694366865301)
      ·
        refine ⟨13133506769670220048446811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 280181477752964694366865301 13133506769670220048446811)
        ·
          refine ⟨19700260154505330072670217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13133506769670220048446811 19700260154505330072670217)
          ·
            refine ⟨14775195115878997554502663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19700260154505330072670217 14775195115878997554502663)
            ·
              refine ⟨22162792673818496331753995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14775195115878997554502663 22162792673818496331753995)
              ·
                refine ⟨33244189010727744497630993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22162792673818496331753995 33244189010727744497630993)
                ·
                  refine ⟨24933141758045808373223245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33244189010727744497630993 24933141758045808373223245)
                  ·
                    refine ⟨9349928159267178139958717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24933141758045808373223245 9349928159267178139958717)
                    ·
                      refine ⟨3506223059725191802484519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9349928159267178139958717 3506223059725191802484519)
                      ·
                        rfl

theorem cell23_6828345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_6828345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828345 prefixEnd_6828345 := by exact prefixLift 6828345
  have htrace : WordTrace (prefixWord ++ tailWord_6828345) baseStart_6828345 baseEnd_6828345 := by
    simpa [prefixWord, tailWord_6828345, baseEnd_6828345] using wordTrace_append hprefix tailTrace_6828345
  have hstable : (prefixWord ++ tailWord_6828345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828345).length < 2 ^ (prefixWord ++ tailWord_6828345).sum := by decide
  have hdescent : baseEnd_6828345 < baseStart_6828345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828368 : List Nat := [2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 4]
def baseStart_6828368 : Nat := 118140960795 + 6828368 * 2 ^ 59
def prefixEnd_6828368 : Nat := 4983230072969 + 3 ^ 40 * 6828368 * 2
def baseEnd_6828368 : Nat := 3506234869780245212496913

theorem tailTrace_6828368 : CollatzResearch.WordTrace tailWord_6828368 prefixEnd_6828368 3506234869780245212496913 := by
  unfold tailWord_6828368
  simp only [CollatzResearch.WordTrace]
  refine ⟨124525520662998201627094879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166034027550664268836126505 124525520662998201627094879)
  ·
    refine ⟨186788280994497302440642319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124525520662998201627094879 186788280994497302440642319)
    ·
      refine ⟨280182421491745953660963479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186788280994497302440642319 280182421491745953660963479)
      ·
        refine ⟨420273632237618930491445219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280182421491745953660963479 420273632237618930491445219)
        ·
          refine ⟨630410448356428395737167829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420273632237618930491445219 630410448356428395737167829)
          ·
            refine ⟨14775244883353790525089871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 630410448356428395737167829 14775244883353790525089871)
            ·
              refine ⟨22162867325030685787634807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14775244883353790525089871 22162867325030685787634807)
              ·
                refine ⟨33244300987546028681452211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22162867325030685787634807 33244300987546028681452211)
                ·
                  refine ⟨49866451481319043022178317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33244300987546028681452211 49866451481319043022178317)
                  ·
                    refine ⟨18699919305494641133316869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49866451481319043022178317 18699919305494641133316869)
                    ·
                      refine ⟨3506234869780245212496913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18699919305494641133316869 3506234869780245212496913)
                      ·
                        rfl

theorem cell23_6828368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 4].length) (baseStart_6828368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828368 prefixEnd_6828368 := by exact prefixLift 6828368
  have htrace : WordTrace (prefixWord ++ tailWord_6828368) baseStart_6828368 baseEnd_6828368 := by
    simpa [prefixWord, tailWord_6828368, baseEnd_6828368] using wordTrace_append hprefix tailTrace_6828368
  have hstable : (prefixWord ++ tailWord_6828368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828368).length < 2 ^ (prefixWord ++ tailWord_6828368).sum := by decide
  have hdescent : baseEnd_6828368 < baseStart_6828368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828371 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 5]
def baseStart_6828371 : Nat := 118140960795 + 6828371 * 2 ^ 59
def prefixEnd_6828371 : Nat := 4983230072969 + 3 ^ 40 * 6828371 * 2
def baseEnd_6828371 : Nat := 3506236410222208700759399

theorem tailTrace_6828371 : CollatzResearch.WordTrace tailWord_6828371 prefixEnd_6828371 3506236410222208700759399 := by
  unfold tailWord_6828371
  simp only [CollatzResearch.WordTrace]
  refine ⟨249051150744985534766548967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166034100496657023177699311 249051150744985534766548967)
  ·
    refine ⟨373576726117478302149823451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249051150744985534766548967 373576726117478302149823451)
    ·
      refine ⟨560365089176217453224735177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373576726117478302149823451 560365089176217453224735177)
      ·
        refine ⟨420273816882163089918551383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 560365089176217453224735177 420273816882163089918551383)
        ·
          refine ⟨630410725323244634877827075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420273816882163089918551383 630410725323244634877827075)
          ·
            refine ⟨945616087984866952316740613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630410725323244634877827075 945616087984866952316740613)
            ·
              refine ⟨177303016497162553559388865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 945616087984866952316740613 177303016497162553559388865)
              ·
                refine ⟨132977262372871915169541649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177303016497162553559388865 132977262372871915169541649)
                ·
                  refine ⟨99732946779653936377156237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132977262372871915169541649 99732946779653936377156237)
                  ·
                    refine ⟨37399855042370226141433589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99732946779653936377156237 37399855042370226141433589)
                    ·
                      refine ⟨3506236410222208700759399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37399855042370226141433589 3506236410222208700759399)
                      ·
                        rfl

theorem cell23_6828371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 5].length) (baseStart_6828371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828371 prefixEnd_6828371 := by exact prefixLift 6828371
  have htrace : WordTrace (prefixWord ++ tailWord_6828371) baseStart_6828371 baseEnd_6828371 := by
    simpa [prefixWord, tailWord_6828371, baseEnd_6828371] using wordTrace_append hprefix tailTrace_6828371
  have hstable : (prefixWord ++ tailWord_6828371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828371).length < 2 ^ (prefixWord ++ tailWord_6828371).sum := by decide
  have hdescent : baseEnd_6828371 < baseStart_6828371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828378 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 7, 4]
def baseStart_6828378 : Nat := 118140960795 + 6828378 * 2 ^ 59
def prefixEnd_6828378 : Nat := 4983230072969 + 3 ^ 40 * 6828378 * 2
def baseEnd_6828378 : Nat := 1168746668195596724457289

theorem tailTrace_6828378 : CollatzResearch.WordTrace tailWord_6828378 prefixEnd_6828378 1168746668195596724457289 := by
  unfold tailWord_6828378
  simp only [CollatzResearch.WordTrace]
  refine ⟨62262851513990043740513447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166034270703973449974702525 62262851513990043740513447)
  ·
    refine ⟨93394277270985065610770171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62262851513990043740513447 93394277270985065610770171)
    ·
      refine ⟨140091415906477598416155257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93394277270985065610770171 140091415906477598416155257)
      ·
        refine ⟨105068561929858198812116443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140091415906477598416155257 105068561929858198812116443)
        ·
          refine ⟨157602842894787298218174665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105068561929858198812116443 157602842894787298218174665)
          ·
            refine ⟨118202132171090473663630999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157602842894787298218174665 118202132171090473663630999)
            ·
              refine ⟨177303198256635710495446499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118202132171090473663630999 177303198256635710495446499)
              ·
                refine ⟨265954797384953565743169749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177303198256635710495446499 265954797384953565743169749)
                ·
                  refine ⟨6233315563709849197105541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 265954797384953565743169749 6233315563709849197105541)
                  ·
                    refine ⟨1168746668195596724457289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6233315563709849197105541 1168746668195596724457289)
                    ·
                      rfl

theorem cell23_6828378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 7, 4].length) (baseStart_6828378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828378 prefixEnd_6828378 := by exact prefixLift 6828378
  have htrace : WordTrace (prefixWord ++ tailWord_6828378) baseStart_6828378 baseEnd_6828378 := by
    simpa [prefixWord, tailWord_6828378, baseEnd_6828378] using wordTrace_append hprefix tailTrace_6828378
  have hstable : (prefixWord ++ tailWord_6828378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828378).length < 2 ^ (prefixWord ++ tailWord_6828378).sum := by decide
  have hdescent : baseEnd_6828378 < baseStart_6828378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828405 : List Nat := [1, 3, 4, 1, 2, 1, 1, 2, 1, 4, 3]
def baseStart_6828405 : Nat := 118140960795 + 6828405 * 2 ^ 59
def prefixEnd_6828405 : Nat := 4983230072969 + 3 ^ 40 * 6828405 * 2
def baseEnd_6828405 : Nat := 3506253868564461567734243

theorem tailTrace_6828405 : CollatzResearch.WordTrace tailWord_6828405 prefixEnd_6828405 3506253868564461567734243 := by
  unfold tailWord_6828405
  simp only [CollatzResearch.WordTrace]
  refine ⟨249052390826862358573286669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166034927217908239048857779 249052390826862358573286669)
  ·
    refine ⟨93394646560073384464982501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249052390826862358573286669 93394646560073384464982501)
    ·
      refine ⟨17511496230013759587184219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93394646560073384464982501 17511496230013759587184219)
      ·
        refine ⟨26267244345020639380776329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17511496230013759587184219 26267244345020639380776329)
        ·
          refine ⟨19700433258765479535582247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26267244345020639380776329 19700433258765479535582247)
          ·
            refine ⟨29550649888148219303373371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19700433258765479535582247 29550649888148219303373371)
            ·
              refine ⟨44325974832222328955060057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29550649888148219303373371 44325974832222328955060057)
              ·
                refine ⟨33244481124166746716295043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44325974832222328955060057 33244481124166746716295043)
                ·
                  refine ⟨49866721686250120074442565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33244481124166746716295043 49866721686250120074442565)
                  ·
                    refine ⟨9350010316171897513957981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49866721686250120074442565 9350010316171897513957981)
                    ·
                      refine ⟨3506253868564461567734243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9350010316171897513957981 3506253868564461567734243)
                      ·
                        rfl

theorem cell23_6828405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_6828405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828405 prefixEnd_6828405 := by exact prefixLift 6828405
  have htrace : WordTrace (prefixWord ++ tailWord_6828405) baseStart_6828405 baseEnd_6828405 := by
    simpa [prefixWord, tailWord_6828405, baseEnd_6828405] using wordTrace_append hprefix tailTrace_6828405
  have hstable : (prefixWord ++ tailWord_6828405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828405).length < 2 ^ (prefixWord ++ tailWord_6828405).sum := by decide
  have hdescent : baseEnd_6828405 < baseStart_6828405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828452 : List Nat := [2, 3, 1, 2, 1, 1, 5, 1, 3, 1, 3]
def baseStart_6828452 : Nat := 118140960795 + 6828452 * 2 ^ 59
def prefixEnd_6828452 : Nat := 4983230072969 + 3 ^ 40 * 6828452 * 2
def baseEnd_6828452 : Nat := 3506278002155222883846527

theorem tailTrace_6828452 : CollatzResearch.WordTrace tailWord_6828452 prefixEnd_6828452 3506278002155222883846527 := by
  unfold tailWord_6828452
  simp only [CollatzResearch.WordTrace]
  refine ⟨124527052528846042800123805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166036070038461390400165073 124527052528846042800123805)
  ·
    refine ⟨46697644698317266050046427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124527052528846042800123805 46697644698317266050046427)
    ·
      refine ⟨70046467047475899075069641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46697644698317266050046427 70046467047475899075069641)
      ·
        refine ⟨52534850285606924306302231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70046467047475899075069641 52534850285606924306302231)
        ·
          refine ⟨78802275428410386459453347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52534850285606924306302231 78802275428410386459453347)
          ·
            refine ⟨118203413142615579689180021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78802275428410386459453347 118203413142615579689180021)
            ·
              refine ⟨11081569982120210595860627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118203413142615579689180021 11081569982120210595860627)
              ·
                refine ⟨16622354973180315893790941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11081569982120210595860627 16622354973180315893790941)
                ·
                  refine ⟨6233383114942618460171603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16622354973180315893790941 6233383114942618460171603)
                  ·
                    refine ⟨9350074672413927690257405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6233383114942618460171603 9350074672413927690257405)
                    ·
                      refine ⟨3506278002155222883846527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9350074672413927690257405 3506278002155222883846527)
                      ·
                        rfl

theorem cell23_6828452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_6828452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828452 prefixEnd_6828452 := by exact prefixLift 6828452
  have htrace : WordTrace (prefixWord ++ tailWord_6828452) baseStart_6828452 baseEnd_6828452 := by
    simpa [prefixWord, tailWord_6828452, baseEnd_6828452] using wordTrace_append hprefix tailTrace_6828452
  have hstable : (prefixWord ++ tailWord_6828452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828452).length < 2 ^ (prefixWord ++ tailWord_6828452).sum := by decide
  have hdescent : baseEnd_6828452 < baseStart_6828452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828509 : List Nat := [1, 4, 3, 1, 1, 1, 2, 3, 3, 2, 2]
def baseStart_6828509 : Nat := 118140960795 + 6828509 * 2 ^ 59
def prefixEnd_6828509 : Nat := 4983230072969 + 3 ^ 40 * 6828509 * 2
def baseEnd_6828509 : Nat := 3506307270552529160833765

theorem tailTrace_6828509 : CollatzResearch.WordTrace tailWord_6828509 prefixEnd_6828509 3506307270552529160833765 := by
  unfold tailWord_6828509
  simp only [CollatzResearch.WordTrace]
  refine ⟨249056184018485584335072581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166037456012323722890048387 249056184018485584335072581)
  ·
    refine ⟨46698034503466047062826109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249056184018485584335072581 46698034503466047062826109)
    ·
      refine ⟨17511762938799767648559791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46698034503466047062826109 17511762938799767648559791)
      ·
        refine ⟨26267644408199651472839687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17511762938799767648559791 26267644408199651472839687)
        ·
          refine ⟨39401466612299477209259531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26267644408199651472839687 39401466612299477209259531)
          ·
            refine ⟨59102199918449215813889297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39401466612299477209259531 59102199918449215813889297)
            ·
              refine ⟨44326649938836911860416973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59102199918449215813889297 44326649938836911860416973)
              ·
                refine ⟨16622493727063841947656365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44326649938836911860416973 16622493727063841947656365)
                ·
                  refine ⟨6233435147648940730371137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16622493727063841947656365 6233435147648940730371137)
                  ·
                    refine ⟨4675076360736705547778353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6233435147648940730371137 4675076360736705547778353)
                    ·
                      refine ⟨3506307270552529160833765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4675076360736705547778353 3506307270552529160833765)
                      ·
                        rfl

theorem cell23_6828509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_6828509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828509 prefixEnd_6828509 := by exact prefixLift 6828509
  have htrace : WordTrace (prefixWord ++ tailWord_6828509) baseStart_6828509 baseEnd_6828509 := by
    simpa [prefixWord, tailWord_6828509, baseEnd_6828509] using wordTrace_append hprefix tailTrace_6828509
  have hstable : (prefixWord ++ tailWord_6828509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828509).length < 2 ^ (prefixWord ++ tailWord_6828509).sum := by decide
  have hdescent : baseEnd_6828509 < baseStart_6828509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828522 : List Nat := [3, 1, 3, 1, 3, 2, 2, 1, 1, 2, 4]
def baseStart_6828522 : Nat := 118140960795 + 6828522 * 2 ^ 59
def prefixEnd_6828522 : Nat := 4983230072969 + 3 ^ 40 * 6828522 * 2
def baseEnd_6828522 : Nat := 3506313945801037609971205

theorem tailTrace_6828522 : CollatzResearch.WordTrace tailWord_6828522 prefixEnd_6828522 3506313945801037609971205 := by
  unfold tailWord_6828522
  simp only [CollatzResearch.WordTrace]
  refine ⟨62264164541859621888823955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166037772111625658370197213 62264164541859621888823955)
  ·
    refine ⟨93396246812789432833235933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62264164541859621888823955 93396246812789432833235933)
    ·
      refine ⟨35023592554796037312463475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93396246812789432833235933 35023592554796037312463475)
      ·
        refine ⟨52535388832194055968695213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35023592554796037312463475 52535388832194055968695213)
        ·
          refine ⟨19700770812072770988260705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52535388832194055968695213 19700770812072770988260705)
          ·
            refine ⟨14775578109054578241195529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19700770812072770988260705 14775578109054578241195529)
            ·
              refine ⟨11081683581790933680896647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14775578109054578241195529 11081683581790933680896647)
              ·
                refine ⟨16622525372686400521344971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11081683581790933680896647 16622525372686400521344971)
                ·
                  refine ⟨24933788059029600782017457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16622525372686400521344971 24933788059029600782017457)
                  ·
                    refine ⟨18700341044272200586513093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24933788059029600782017457 18700341044272200586513093)
                    ·
                      refine ⟨3506313945801037609971205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18700341044272200586513093 3506313945801037609971205)
                      ·
                        rfl

theorem cell23_6828522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_6828522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828522 prefixEnd_6828522 := by exact prefixLift 6828522
  have htrace : WordTrace (prefixWord ++ tailWord_6828522) baseStart_6828522 baseEnd_6828522 := by
    simpa [prefixWord, tailWord_6828522, baseEnd_6828522] using wordTrace_append hprefix tailTrace_6828522
  have hstable : (prefixWord ++ tailWord_6828522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828522).length < 2 ^ (prefixWord ++ tailWord_6828522).sum := by decide
  have hdescent : baseEnd_6828522 < baseStart_6828522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828528 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 2, 7]
def baseStart_6828528 : Nat := 118140960795 + 6828528 * 2 ^ 59
def prefixEnd_6828528 : Nat := 4983230072969 + 3 ^ 40 * 6828528 * 2
def baseEnd_6828528 : Nat := 1168772342228321528832059

theorem tailTrace_6828528 : CollatzResearch.WordTrace tailWord_6828528 prefixEnd_6828528 1168772342228321528832059 := by
  unfold tailWord_6828528
  simp only [CollatzResearch.WordTrace]
  refine ⟨124528438502708375290007119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166037918003611167053342825 124528438502708375290007119)
  ·
    refine ⟨186792657754062562935010679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124528438502708375290007119 186792657754062562935010679)
    ·
      refine ⟨280188986631093844402516019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186792657754062562935010679 280188986631093844402516019)
      ·
        refine ⟨420283479946640766603774029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280188986631093844402516019 420283479946640766603774029)
        ·
          refine ⟨157606304979990287476415261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 420283479946640766603774029 157606304979990287476415261)
          ·
            refine ⟨59102364367496357803655723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157606304979990287476415261 59102364367496357803655723)
            ·
              refine ⟨88653546551244536705483585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59102364367496357803655723 88653546551244536705483585)
              ·
                refine ⟨66490159913433402529112689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88653546551244536705483585 66490159913433402529112689)
                ·
                  refine ⟨49867619935075051896834517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66490159913433402529112689 49867619935075051896834517)
                  ·
                    refine ⟨1168772342228321528832059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49867619935075051896834517 1168772342228321528832059)
                    ·
                      rfl

theorem cell23_6828528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 2, 7].length) (baseStart_6828528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828528 prefixEnd_6828528 := by exact prefixLift 6828528
  have htrace : WordTrace (prefixWord ++ tailWord_6828528) baseStart_6828528 baseEnd_6828528 := by
    simpa [prefixWord, tailWord_6828528, baseEnd_6828528] using wordTrace_append hprefix tailTrace_6828528
  have hstable : (prefixWord ++ tailWord_6828528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828528).length < 2 ^ (prefixWord ++ tailWord_6828528).sum := by decide
  have hdescent : baseEnd_6828528 < baseStart_6828528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828546 : List Nat := [3, 4, 1, 2, 2, 1, 1, 3, 1, 2, 3]
def baseStart_6828546 : Nat := 118140960795 + 6828546 * 2 ^ 59
def prefixEnd_6828546 : Nat := 4983230072969 + 3 ^ 40 * 6828546 * 2
def baseEnd_6828546 : Nat := 3506326269336745516071095

theorem tailTrace_6828546 : CollatzResearch.WordTrace tailWord_6828546 prefixEnd_6828546 3506326269336745516071095 := by
  unfold tailWord_6828546
  simp only [CollatzResearch.WordTrace]
  refine ⟨62264383379837884913542373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166038355679567693102779661 62264383379837884913542373)
  ·
    refine ⟨11674571883719603421289195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62264383379837884913542373 11674571883719603421289195)
    ·
      refine ⟨17511857825579405131933793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11674571883719603421289195 17511857825579405131933793)
      ·
        refine ⟨13133893369184553848950345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17511857825579405131933793 13133893369184553848950345)
        ·
          refine ⟨9850420026888415386712759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13133893369184553848950345 9850420026888415386712759)
          ·
            refine ⟨14775630040332623080069139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9850420026888415386712759 14775630040332623080069139)
            ·
              refine ⟨22163445060498934620103709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14775630040332623080069139 22163445060498934620103709)
              ·
                refine ⟨8311291897687100482538891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22163445060498934620103709 8311291897687100482538891)
                ·
                  refine ⟨12466937846530650723808337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8311291897687100482538891 12466937846530650723808337)
                  ·
                    refine ⟨9350203384897988042856253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12466937846530650723808337 9350203384897988042856253)
                    ·
                      refine ⟨3506326269336745516071095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9350203384897988042856253 3506326269336745516071095)
                      ·
                        rfl

theorem cell23_6828546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_6828546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828546 prefixEnd_6828546 := by exact prefixLift 6828546
  have htrace : WordTrace (prefixWord ++ tailWord_6828546) baseStart_6828546 baseEnd_6828546 := by
    simpa [prefixWord, tailWord_6828546, baseEnd_6828546] using wordTrace_append hprefix tailTrace_6828546
  have hstable : (prefixWord ++ tailWord_6828546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828546).length < 2 ^ (prefixWord ++ tailWord_6828546).sum := by decide
  have hdescent : baseEnd_6828546 < baseStart_6828546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828576 : List Nat := [2, 1, 1, 6, 3, 1, 1, 1, 1, 3, 3]
def baseStart_6828576 : Nat := 118140960795 + 6828576 * 2 ^ 59
def prefixEnd_6828576 : Nat := 4983230072969 + 3 ^ 40 * 6828576 * 2
def baseEnd_6828576 : Nat := 3506341673756380398695957

theorem tailTrace_6828576 : CollatzResearch.WordTrace tailWord_6828576 prefixEnd_6828576 3506341673756380398695957 := by
  unfold tailWord_6828576
  simp only [CollatzResearch.WordTrace]
  refine ⟨124529313854621427388880791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166039085139495236518507721 124529313854621427388880791)
  ·
    refine ⟨186793970781932141083321187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124529313854621427388880791 186793970781932141083321187)
    ·
      refine ⟨280190956172898211624981781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186793970781932141083321187 280190956172898211624981781)
      ·
        refine ⟨13133951070604603669921021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 280190956172898211624981781 13133951070604603669921021)
        ·
          refine ⟨4925231651476726376220383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13133951070604603669921021 4925231651476726376220383)
          ·
            refine ⟨7387847477215089564330575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4925231651476726376220383 7387847477215089564330575)
            ·
              refine ⟨11081771215822634346495863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7387847477215089564330575 11081771215822634346495863)
              ·
                refine ⟨16622656823733951519743795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11081771215822634346495863 16622656823733951519743795)
                ·
                  refine ⟨24933985235600927279615693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16622656823733951519743795 24933985235600927279615693)
                  ·
                    refine ⟨9350244463350347729855885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24933985235600927279615693 9350244463350347729855885)
                    ·
                      refine ⟨3506341673756380398695957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9350244463350347729855885 3506341673756380398695957)
                      ·
                        rfl

theorem cell23_6828576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_6828576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828576 prefixEnd_6828576 := by exact prefixLift 6828576
  have htrace : WordTrace (prefixWord ++ tailWord_6828576) baseStart_6828576 baseEnd_6828576 := by
    simpa [prefixWord, tailWord_6828576, baseEnd_6828576] using wordTrace_append hprefix tailTrace_6828576
  have hstable : (prefixWord ++ tailWord_6828576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828576).length < 2 ^ (prefixWord ++ tailWord_6828576).sum := by decide
  have hdescent : baseEnd_6828576 < baseStart_6828576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828586 : List Nat := [3, 1, 4, 1, 1, 3, 2, 2, 1, 3, 2]
def baseStart_6828586 : Nat := 118140960795 + 6828586 * 2 ^ 59
def prefixEnd_6828586 : Nat := 4983230072969 + 3 ^ 40 * 6828586 * 2
def baseEnd_6828586 : Nat := 3506346808562925359570911

theorem tailTrace_6828586 : CollatzResearch.WordTrace tailWord_6828586 prefixEnd_6828586 3506346808562925359570911 := by
  unfold tailWord_6828586
  simp only [CollatzResearch.WordTrace]
  refine ⟨62264748109801656621406403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166039328292804417657083741 62264748109801656621406403)
  ·
    refine ⟨93397122164702484932109605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62264748109801656621406403 93397122164702484932109605)
    ·
      refine ⟨17511960405881715924770551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93397122164702484932109605 17511960405881715924770551)
      ·
        refine ⟨26267940608822573887155827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17511960405881715924770551 26267940608822573887155827)
        ·
          refine ⟨39401910913233860830733741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26267940608822573887155827 39401910913233860830733741)
          ·
            refine ⟨14775716592462697811525153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39401910913233860830733741 14775716592462697811525153)
            ·
              refine ⟨11081787444347023358643865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14775716592462697811525153 11081787444347023358643865)
              ·
                refine ⟨8311340583260267518982899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11081787444347023358643865 8311340583260267518982899)
                ·
                  refine ⟨12467010874890401278474349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8311340583260267518982899 12467010874890401278474349)
                  ·
                    refine ⟨4675129078083900479427881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12467010874890401278474349 4675129078083900479427881)
                    ·
                      refine ⟨3506346808562925359570911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4675129078083900479427881 3506346808562925359570911)
                      ·
                        rfl

theorem cell23_6828586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_6828586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828586 prefixEnd_6828586 := by exact prefixLift 6828586
  have htrace : WordTrace (prefixWord ++ tailWord_6828586) baseStart_6828586 baseEnd_6828586 := by
    simpa [prefixWord, tailWord_6828586, baseEnd_6828586] using wordTrace_append hprefix tailTrace_6828586
  have hstable : (prefixWord ++ tailWord_6828586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828586).length < 2 ^ (prefixWord ++ tailWord_6828586).sum := by decide
  have hdescent : baseEnd_6828586 < baseStart_6828586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828622 : List Nat := [4, 1, 1, 1, 1, 2, 2, 6, 5]
def baseStart_6828622 : Nat := 118140960795 + 6828622 * 2 ^ 59
def prefixEnd_6828622 : Nat := 4983230072969 + 3 ^ 40 * 6828622 * 2
def baseEnd_6828622 : Nat := 389596143762943024302305

theorem tailTrace_6828622 : CollatzResearch.WordTrace tailWord_6828622 prefixEnd_6828622 389596143762943024302305 := by
  unfold tailWord_6828622
  simp only [CollatzResearch.WordTrace]
  refine ⟨31132538183384525579242015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166040203644717469755957413 31132538183384525579242015)
  ·
    refine ⟨46698807275076788368863023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31132538183384525579242015 46698807275076788368863023)
    ·
      refine ⟨70048210912615182553294535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46698807275076788368863023 70048210912615182553294535)
      ·
        refine ⟨105072316368922773829941803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70048210912615182553294535 105072316368922773829941803)
        ·
          refine ⟨157608474553384160744912705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105072316368922773829941803 157608474553384160744912705)
          ·
            refine ⟨118206355915038120558684529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157608474553384160744912705 118206355915038120558684529)
            ·
              refine ⟨88654766936278590419013397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118206355915038120558684529 88654766936278590419013397)
              ·
                refine ⟨4155692200138058925891253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88654766936278590419013397 4155692200138058925891253)
                ·
                  refine ⟨389596143762943024302305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4155692200138058925891253 389596143762943024302305)
                  ·
                    rfl

theorem cell23_6828622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 6, 5].length) (baseStart_6828622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828622 prefixEnd_6828622 := by exact prefixLift 6828622
  have htrace : WordTrace (prefixWord ++ tailWord_6828622) baseStart_6828622 baseEnd_6828622 := by
    simpa [prefixWord, tailWord_6828622, baseEnd_6828622] using wordTrace_append hprefix tailTrace_6828622
  have hstable : (prefixWord ++ tailWord_6828622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828622).length < 2 ^ (prefixWord ++ tailWord_6828622).sum := by decide
  have hdescent : baseEnd_6828622 < baseStart_6828622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828655 : List Nat := [1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 4]
def baseStart_6828655 : Nat := 118140960795 + 6828655 * 2 ^ 59
def prefixEnd_6828655 : Nat := 4983230072969 + 3 ^ 40 * 6828655 * 2
def baseEnd_6828655 : Nat := 3506382238728085589608093

theorem tailTrace_6828655 : CollatzResearch.WordTrace tailWord_6828655 prefixEnd_6828655 3506382238728085589608093 := by
  unfold tailWord_6828655
  simp only [CollatzResearch.WordTrace]
  refine ⟨249061509075956651269887419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166041006050637767513258279 249061509075956651269887419)
  ·
    refine ⟨373592263613934976904831129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249061509075956651269887419 373592263613934976904831129)
    ·
      refine ⟨280194197710451232678623347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373592263613934976904831129 280194197710451232678623347)
      ·
        refine ⟨420291296565676849017935021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280194197710451232678623347 420291296565676849017935021)
        ·
          refine ⟨157609236212128818381725633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 420291296565676849017935021 157609236212128818381725633)
          ·
            refine ⟨118206927159096613786294225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157609236212128818381725633 118206927159096613786294225)
            ·
              refine ⟨88655195369322460339720669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118206927159096613786294225 88655195369322460339720669)
              ·
                refine ⟨33245698263495922627395251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88655195369322460339720669 33245698263495922627395251)
                ·
                  refine ⟨49868547395243883941092877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33245698263495922627395251 49868547395243883941092877)
                  ·
                    refine ⟨18700705273216456477909829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49868547395243883941092877 18700705273216456477909829)
                    ·
                      refine ⟨3506382238728085589608093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18700705273216456477909829 3506382238728085589608093)
                      ·
                        rfl

theorem cell23_6828655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 4].length) (baseStart_6828655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828655 prefixEnd_6828655 := by exact prefixLift 6828655
  have htrace : WordTrace (prefixWord ++ tailWord_6828655) baseStart_6828655 baseEnd_6828655 := by
    simpa [prefixWord, tailWord_6828655, baseEnd_6828655] using wordTrace_append hprefix tailTrace_6828655
  have hstable : (prefixWord ++ tailWord_6828655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828655).length < 2 ^ (prefixWord ++ tailWord_6828655).sum := by decide
  have hdescent : baseEnd_6828655 < baseStart_6828655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828672 : List Nat := [2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 4]
def baseStart_6828672 : Nat := 118140960795 + 6828672 * 2 ^ 59
def prefixEnd_6828672 : Nat := 4983230072969 + 3 ^ 40 * 6828672 * 2
def baseEnd_6828672 : Nat := 3506390967899212023095515

theorem tailTrace_6828672 : CollatzResearch.WordTrace tailWord_6828672 prefixEnd_6828672 3506390967899212023095515 := by
  unfold tailWord_6828672
  simp only [CollatzResearch.WordTrace]
  refine ⟨124531064558447531586628135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166041419411263375448837513 124531064558447531586628135)
  ·
    refine ⟨186796596837671297379942203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124531064558447531586628135 186796596837671297379942203)
    ·
      refine ⟨280194895256506946069913305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186796596837671297379942203 280194895256506946069913305)
      ·
        refine ⟨210146171442380209552434979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280194895256506946069913305 210146171442380209552434979)
        ·
          refine ⟨315219257163570314328652469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210146171442380209552434979 315219257163570314328652469)
          ·
            refine ⟨29551805359084716968311169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 315219257163570314328652469 29551805359084716968311169)
            ·
              refine ⟨22163854019313537726233377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29551805359084716968311169 22163854019313537726233377)
              ·
                refine ⟨16622890514485153294675033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22163854019313537726233377 16622890514485153294675033)
                ·
                  refine ⟨12467167885863864971006275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16622890514485153294675033 12467167885863864971006275)
                  ·
                    refine ⟨18700751828795797456509413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12467167885863864971006275 18700751828795797456509413)
                    ·
                      refine ⟨3506390967899212023095515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18700751828795797456509413 3506390967899212023095515)
                      ·
                        rfl

theorem cell23_6828672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_6828672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828672 prefixEnd_6828672 := by exact prefixLift 6828672
  have htrace : WordTrace (prefixWord ++ tailWord_6828672) baseStart_6828672 baseEnd_6828672 := by
    simpa [prefixWord, tailWord_6828672, baseEnd_6828672] using wordTrace_append hprefix tailTrace_6828672
  have hstable : (prefixWord ++ tailWord_6828672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828672).length < 2 ^ (prefixWord ++ tailWord_6828672).sum := by decide
  have hdescent : baseEnd_6828672 < baseStart_6828672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828759 : List Nat := [1, 1, 3, 2, 1, 5, 2, 2, 1, 5]
def baseStart_6828759 : Nat := 118140960795 + 6828759 * 2 ^ 59
def prefixEnd_6828759 : Nat := 4983230072969 + 3 ^ 40 * 6828759 * 2
def baseEnd_6828759 : Nat := 1168811880238717727569205

theorem tailTrace_6828759 : CollatzResearch.WordTrace tailWord_6828759 prefixEnd_6828759 1168811880238717727569205 := by
  unfold tailWord_6828759
  simp only [CollatzResearch.WordTrace]
  refine ⟨249065302267579877031673331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166043534845053251354448887 249065302267579877031673331)
  ·
    refine ⟨373597953401369815547509997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249065302267579877031673331 373597953401369815547509997)
    ·
      refine ⟨140099232525513680830316249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373597953401369815547509997 140099232525513680830316249)
      ·
        refine ⟨105074424394135260622737187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140099232525513680830316249 105074424394135260622737187)
        ·
          refine ⟨157611636591202890934105781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105074424394135260622737187 157611636591202890934105781)
          ·
            refine ⟨14776090930425271025072417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157611636591202890934105781 14776090930425271025072417)
            ·
              refine ⟨11082068197818953268804313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14776090930425271025072417 11082068197818953268804313)
              ·
                refine ⟨8311551148364214951603235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11082068197818953268804313 8311551148364214951603235)
                ·
                  refine ⟨12467326722546322427404853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8311551148364214951603235 12467326722546322427404853)
                  ·
                    refine ⟨1168811880238717727569205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12467326722546322427404853 1168811880238717727569205)
                    ·
                      rfl

theorem cell23_6828759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 5].length) (baseStart_6828759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828759 prefixEnd_6828759 := by exact prefixLift 6828759
  have htrace : WordTrace (prefixWord ++ tailWord_6828759) baseStart_6828759 baseEnd_6828759 := by
    simpa [prefixWord, tailWord_6828759, baseEnd_6828759] using wordTrace_append hprefix tailTrace_6828759
  have hstable : (prefixWord ++ tailWord_6828759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828759).length < 2 ^ (prefixWord ++ tailWord_6828759).sum := by decide
  have hdescent : baseEnd_6828759 < baseStart_6828759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828773 : List Nat := [1, 3, 1, 4, 1, 2, 3, 3, 1, 1, 3]
def baseStart_6828773 : Nat := 118140960795 + 6828773 * 2 ^ 59
def prefixEnd_6828773 : Nat := 4983230072969 + 3 ^ 40 * 6828773 * 2
def baseEnd_6828773 : Nat := 3506442829445316127932551

theorem tailTrace_6828773 : CollatzResearch.WordTrace tailWord_6828773 prefixEnd_6828773 3506442829445316127932551 := by
  unfold tailWord_6828773
  simp only [CollatzResearch.WordTrace]
  refine ⟨249065812889529157422682973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166043875259686104948455315 249065812889529157422682973)
  ·
    refine ⟨93399679833573434033506115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249065812889529157422682973 93399679833573434033506115)
    ·
      refine ⟨140099519750360151050259173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93399679833573434033506115 140099519750360151050259173)
      ·
        refine ⟨26268659953192528321923595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140099519750360151050259173 26268659953192528321923595)
        ·
          refine ⟨39402989929788792482885393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26268659953192528321923595 39402989929788792482885393)
          ·
            refine ⟨29552242447341594362164045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39402989929788792482885393 29552242447341594362164045)
            ·
              refine ⟨11082090917753097885811517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29552242447341594362164045 11082090917753097885811517)
              ·
                refine ⟨4155784094157411707179319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11082090917753097885811517 4155784094157411707179319)
                ·
                  refine ⟨6233676141236117560768979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4155784094157411707179319 6233676141236117560768979)
                  ·
                    refine ⟨9350514211854176341153469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6233676141236117560768979 9350514211854176341153469)
                    ·
                      refine ⟨3506442829445316127932551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9350514211854176341153469 3506442829445316127932551)
                      ·
                        rfl

theorem cell23_6828773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_6828773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828773 prefixEnd_6828773 := by exact prefixLift 6828773
  have htrace : WordTrace (prefixWord ++ tailWord_6828773) baseStart_6828773 baseEnd_6828773 := by
    simpa [prefixWord, tailWord_6828773, baseEnd_6828773] using wordTrace_append hprefix tailTrace_6828773
  have hstable : (prefixWord ++ tailWord_6828773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828773).length < 2 ^ (prefixWord ++ tailWord_6828773).sum := by decide
  have hdescent : baseEnd_6828773 < baseStart_6828773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828790 : List Nat := [5, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3]
def baseStart_6828790 : Nat := 118140960795 + 6828790 * 2 ^ 59
def prefixEnd_6828790 : Nat := 4983230072969 + 3 ^ 40 * 6828790 * 2
def baseEnd_6828790 : Nat := 3506451558616442561419973

theorem tailTrace_6828790 : CollatzResearch.WordTrace tailWord_6828790 prefixEnd_6828790 3506451558616442561419973 := by
  unfold tailWord_6828790
  simp only [CollatzResearch.WordTrace]
  refine ⟨15566652058154223082878239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166044288620311712884034549 15566652058154223082878239)
  ·
    refine ⟨23349978087231334624317359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15566652058154223082878239 23349978087231334624317359)
    ·
      refine ⟨35024967130847001936476039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23349978087231334624317359 35024967130847001936476039)
      ·
        refine ⟨52537450696270502904714059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35024967130847001936476039 52537450696270502904714059)
        ·
          refine ⟨78806176044405754357071089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52537450696270502904714059 78806176044405754357071089)
          ·
            refine ⟨59104632033304315767803317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78806176044405754357071089 59104632033304315767803317)
            ·
              refine ⟨5541059253122279603231561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59104632033304315767803317 5541059253122279603231561)
              ·
                refine ⟨4155794439841709702423671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5541059253122279603231561 4155794439841709702423671)
                ·
                  refine ⟨6233691659762564553635507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4155794439841709702423671 6233691659762564553635507)
                  ·
                    refine ⟨9350537489643846830453261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6233691659762564553635507 9350537489643846830453261)
                    ·
                      refine ⟨3506451558616442561419973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9350537489643846830453261 3506451558616442561419973)
                      ·
                        rfl

theorem cell23_6828790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_6828790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828790 prefixEnd_6828790 := by exact prefixLift 6828790
  have htrace : WordTrace (prefixWord ++ tailWord_6828790) baseStart_6828790 baseEnd_6828790 := by
    simpa [prefixWord, tailWord_6828790, baseEnd_6828790] using wordTrace_append hprefix tailTrace_6828790
  have hstable : (prefixWord ++ tailWord_6828790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828790).length < 2 ^ (prefixWord ++ tailWord_6828790).sum := by decide
  have hdescent : baseEnd_6828790 < baseStart_6828790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828890 : List Nat := [3, 1, 1, 2, 1, 6, 2, 1, 1, 3, 2]
def baseStart_6828890 : Nat := 118140960795 + 6828890 * 2 ^ 59
def prefixEnd_6828890 : Nat := 4983230072969 + 3 ^ 40 * 6828890 * 2
def baseEnd_6828890 : Nat := 3506502906681892170169513

theorem tailTrace_6828890 : CollatzResearch.WordTrace tailWord_6828890 prefixEnd_6828890 3506502906681892170169513 := by
  unfold tailWord_6828890
  simp only [CollatzResearch.WordTrace]
  refine ⟨62267520057526321601173031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166046720153403524269794749 62267520057526321601173031)
  ·
    refine ⟨93401280086289482401759547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62267520057526321601173031 93401280086289482401759547)
    ·
      refine ⟨140101920129434223602639321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93401280086289482401759547 140101920129434223602639321)
      ·
        refine ⟨105076440097075667701979491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140101920129434223602639321 105076440097075667701979491)
        ·
          refine ⟨157614660145613501552969237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105076440097075667701979491 157614660145613501552969237)
          ·
            refine ⟨7388187194325632885295433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 157614660145613501552969237 7388187194325632885295433)
            ·
              refine ⟨5541140395744224663971575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7388187194325632885295433 5541140395744224663971575)
              ·
                refine ⟨8311710593616336995957363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5541140395744224663971575 8311710593616336995957363)
                ·
                  refine ⟨12467565890424505493936045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8311710593616336995957363 12467565890424505493936045)
                  ·
                    refine ⟨4675337208909189560226017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12467565890424505493936045 4675337208909189560226017)
                    ·
                      refine ⟨3506502906681892170169513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4675337208909189560226017 3506502906681892170169513)
                      ·
                        rfl

theorem cell23_6828890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 1, 3, 2].length) (baseStart_6828890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828890 prefixEnd_6828890 := by exact prefixLift 6828890
  have htrace : WordTrace (prefixWord ++ tailWord_6828890) baseStart_6828890 baseEnd_6828890 := by
    simpa [prefixWord, tailWord_6828890, baseEnd_6828890] using wordTrace_append hprefix tailTrace_6828890
  have hstable : (prefixWord ++ tailWord_6828890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828890).length < 2 ^ (prefixWord ++ tailWord_6828890).sum := by decide
  have hdescent : baseEnd_6828890 < baseStart_6828890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828899 : List Nat := [1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 4]
def baseStart_6828899 : Nat := 118140960795 + 6828899 * 2 ^ 59
def prefixEnd_6828899 : Nat := 4983230072969 + 3 ^ 40 * 6828899 * 2
def baseEnd_6828899 : Nat := 3506507528007782634956971

theorem tailTrace_6828899 : CollatzResearch.WordTrace tailWord_6828899 prefixEnd_6828899 3506507528007782634956971 := by
  unfold tailWord_6828899
  simp only [CollatzResearch.WordTrace]
  refine ⟨249070408487072680941769751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166046938991381787294513167 249070408487072680941769751)
  ·
    refine ⟨373605612730609021412654627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249070408487072680941769751 373605612730609021412654627)
    ·
      refine ⟨560408419095913532118981941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373605612730609021412654627 560408419095913532118981941)
      ·
        refine ⟨52538289290241893636154557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 560408419095913532118981941 52538289290241893636154557)
        ·
          refine ⟨19701858483840710113557959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52538289290241893636154557 19701858483840710113557959)
          ·
            refine ⟨29552787725761065170336939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19701858483840710113557959 29552787725761065170336939)
            ·
              refine ⟨44329181588641597755505409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29552787725761065170336939 44329181588641597755505409)
              ·
                refine ⟨33246886191481198316629057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44329181588641597755505409 33246886191481198316629057)
                ·
                  refine ⟨24935164643610898737471793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33246886191481198316629057 24935164643610898737471793)
                  ·
                    refine ⟨18701373482708174053103845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24935164643610898737471793 18701373482708174053103845)
                    ·
                      refine ⟨3506507528007782634956971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18701373482708174053103845 3506507528007782634956971)
                      ·
                        rfl

theorem cell23_6828899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_6828899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828899 prefixEnd_6828899 := by exact prefixLift 6828899
  have htrace : WordTrace (prefixWord ++ tailWord_6828899) baseStart_6828899 baseEnd_6828899 := by
    simpa [prefixWord, tailWord_6828899, baseEnd_6828899] using wordTrace_append hprefix tailTrace_6828899
  have hstable : (prefixWord ++ tailWord_6828899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828899).length < 2 ^ (prefixWord ++ tailWord_6828899).sum := by decide
  have hdescent : baseEnd_6828899 < baseStart_6828899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828903 : List Nat := [1, 1, 5, 1, 2, 3, 1, 1, 4, 2, 2]
def baseStart_6828903 : Nat := 118140960795 + 6828903 * 2 ^ 59
def prefixEnd_6828903 : Nat := 4983230072969 + 3 ^ 40 * 6828903 * 2
def baseEnd_6828903 : Nat := 3506509581930400619306953

theorem tailTrace_6828903 : CollatzResearch.WordTrace tailWord_6828903 prefixEnd_6828903 3506509581930400619306953 := by
  unfold tailWord_6828903
  simp only [CollatzResearch.WordTrace]
  refine ⟨249070554379058189624915363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166047036252705459749943575 249070554379058189624915363)
  ·
    refine ⟨373605831568587284437373045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249070554379058189624915363 373605831568587284437373045)
    ·
      refine ⟨35025546709555057916003723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 373605831568587284437373045 35025546709555057916003723)
      ·
        refine ⟨52538320064332586874005585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35025546709555057916003723 52538320064332586874005585)
        ·
          refine ⟨39403740048249440155504189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52538320064332586874005585 39403740048249440155504189)
          ·
            refine ⟨14776402518093540058314071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39403740048249440155504189 14776402518093540058314071)
            ·
              refine ⟨22164603777140310087471107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14776402518093540058314071 22164603777140310087471107)
              ·
                refine ⟨33246905665710465131206661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22164603777140310087471107 33246905665710465131206661)
                ·
                  refine ⟨6233794812320712212101249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33246905665710465131206661 6233794812320712212101249)
                  ·
                    refine ⟨4675346109240534159075937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6233794812320712212101249 4675346109240534159075937)
                    ·
                      refine ⟨3506509581930400619306953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4675346109240534159075937 3506509581930400619306953)
                      ·
                        rfl

theorem cell23_6828903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_6828903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828903 prefixEnd_6828903 := by exact prefixLift 6828903
  have htrace : WordTrace (prefixWord ++ tailWord_6828903) baseStart_6828903 baseEnd_6828903 := by
    simpa [prefixWord, tailWord_6828903, baseEnd_6828903] using wordTrace_append hprefix tailTrace_6828903
  have hstable : (prefixWord ++ tailWord_6828903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828903).length < 2 ^ (prefixWord ++ tailWord_6828903).sum := by decide
  have hdescent : baseEnd_6828903 < baseStart_6828903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6828979 : List Nat := [1, 1, 1, 2, 3, 1, 2, 4, 1, 4, 3]
def baseStart_6828979 : Nat := 118140960795 + 6828979 * 2 ^ 59
def prefixEnd_6828979 : Nat := 4983230072969 + 3 ^ 40 * 6828979 * 2
def baseEnd_6828979 : Nat := 3506548606460142321956603

theorem tailTrace_6828979 : CollatzResearch.WordTrace tailWord_6828979 prefixEnd_6828979 3506548606460142321956603 := by
  unfold tailWord_6828979
  simp only [CollatzResearch.WordTrace]
  refine ⟨249073326326782854604681991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166048884217855236403121327 249073326326782854604681991)
  ·
    refine ⟨373609989490174281907022987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249073326326782854604681991 373609989490174281907022987)
    ·
      refine ⟨560414984235261422860534481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373609989490174281907022987 560414984235261422860534481)
      ·
        refine ⟨420311238176446067145400861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 560414984235261422860534481 420311238176446067145400861)
        ·
          refine ⟨157616714316167275179525323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 420311238176446067145400861 157616714316167275179525323)
          ·
            refine ⟨236425071474250912769287985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157616714316167275179525323 236425071474250912769287985)
            ·
              refine ⟨177318803605688184576965989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236425071474250912769287985 177318803605688184576965989)
              ·
                refine ⟨33247275676066534608181123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177318803605688184576965989 33247275676066534608181123)
                ·
                  refine ⟨49870913514099801912271685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33247275676066534608181123 49870913514099801912271685)
                  ·
                    refine ⟨9350796283893712858550941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49870913514099801912271685 9350796283893712858550941)
                    ·
                      refine ⟨3506548606460142321956603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9350796283893712858550941 3506548606460142321956603)
                      ·
                        rfl

theorem cell23_6828979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 4, 3].length) (baseStart_6828979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6828979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6828979 prefixEnd_6828979 := by exact prefixLift 6828979
  have htrace : WordTrace (prefixWord ++ tailWord_6828979) baseStart_6828979 baseEnd_6828979 := by
    simpa [prefixWord, tailWord_6828979, baseEnd_6828979] using wordTrace_append hprefix tailTrace_6828979
  have hstable : (prefixWord ++ tailWord_6828979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6828979).length < 2 ^ (prefixWord ++ tailWord_6828979).sum := by decide
  have hdescent : baseEnd_6828979 < baseStart_6828979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6828979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829016 : List Nat := [2, 1, 2, 2, 2, 4, 2, 2, 6]
def baseStart_6829016 : Nat := 118140960795 + 6829016 * 2 ^ 59
def prefixEnd_6829016 : Nat := 4983230072969 + 3 ^ 40 * 6829016 * 2
def baseEnd_6829016 : Nat := 389618622804928741910437

theorem tailTrace_6829016 : CollatzResearch.WordTrace tailWord_6829016 prefixEnd_6829016 389618622804928741910437 := by
  unfold tailWord_6829016
  simp only [CollatzResearch.WordTrace]
  refine ⟨124537337913824404961889451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166049783885099206615852601 124537337913824404961889451)
  ·
    refine ⟨186806006870736607442834177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124537337913824404961889451 186806006870736607442834177)
    ·
      refine ⟨140104505153052455582125633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186806006870736607442834177 140104505153052455582125633)
      ·
        refine ⟨105078378864789341686594225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140104505153052455582125633 105078378864789341686594225)
        ·
          refine ⟨78808784148592006264945669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105078378864789341686594225 78808784148592006264945669)
          ·
            refine ⟨14776647027861001174677313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78808784148592006264945669 14776647027861001174677313)
            ·
              refine ⟨11082485270895750881007985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14776647027861001174677313 11082485270895750881007985)
              ·
                refine ⟨8311863953171813160755989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11082485270895750881007985 8311863953171813160755989)
                ·
                  refine ⟨389618622804928741910437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8311863953171813160755989 389618622804928741910437)
                  ·
                    rfl

theorem cell23_6829016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 6].length) (baseStart_6829016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829016 prefixEnd_6829016 := by exact prefixLift 6829016
  have htrace : WordTrace (prefixWord ++ tailWord_6829016) baseStart_6829016 baseEnd_6829016 := by
    simpa [prefixWord, tailWord_6829016, baseEnd_6829016] using wordTrace_append hprefix tailTrace_6829016
  have hstable : (prefixWord ++ tailWord_6829016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829016).length < 2 ^ (prefixWord ++ tailWord_6829016).sum := by decide
  have hdescent : baseEnd_6829016 < baseStart_6829016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829119 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 1, 9]
def baseStart_6829119 : Nat := 118140960795 + 6829119 * 2 ^ 59
def prefixEnd_6829119 : Nat := 4983230072969 + 3 ^ 40 * 6829119 * 2
def baseEnd_6829119 : Nat := 1168873497917257258068653

theorem tailTrace_6829119 : CollatzResearch.WordTrace tailWord_6829119 prefixEnd_6829119 1168873497917257258068653 := by
  unfold tailWord_6829119
  simp only [CollatzResearch.WordTrace]
  refine ⟨249078432546275658514778411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166052288364183772343185607 249078432546275658514778411)
  ·
    refine ⟨373617648819413487772167617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249078432546275658514778411 373617648819413487772167617)
    ·
      refine ⟨280213236614560115829125713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373617648819413487772167617 280213236614560115829125713)
      ·
        refine ⟨210159927460920086871844285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280213236614560115829125713 210159927460920086871844285)
        ·
          refine ⟨78809972797845032576941607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210159927460920086871844285 78809972797845032576941607)
          ·
            refine ⟨118214959196767548865412411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78809972797845032576941607 118214959196767548865412411)
            ·
              refine ⟨177322438795151323298118617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118214959196767548865412411 177322438795151323298118617)
              ·
                refine ⟨132991829096363492473588963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177322438795151323298118617 132991829096363492473588963)
                ·
                  refine ⟨199487743644545238710383445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132991829096363492473588963 199487743644545238710383445)
                  ·
                    refine ⟨1168873497917257258068653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 199487743644545238710383445 1168873497917257258068653)
                    ·
                      rfl

theorem cell23_6829119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 9].length) (baseStart_6829119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829119 prefixEnd_6829119 := by exact prefixLift 6829119
  have htrace : WordTrace (prefixWord ++ tailWord_6829119) baseStart_6829119 baseEnd_6829119 := by
    simpa [prefixWord, tailWord_6829119, baseEnd_6829119] using wordTrace_append hprefix tailTrace_6829119
  have hstable : (prefixWord ++ tailWord_6829119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829119).length < 2 ^ (prefixWord ++ tailWord_6829119).sum := by decide
  have hdescent : baseEnd_6829119 < baseStart_6829119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829134 : List Nat := [4, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2]
def baseStart_6829134 : Nat := 118140960795 + 6829134 * 2 ^ 59
def prefixEnd_6829134 : Nat := 4983230072969 + 3 ^ 40 * 6829134 * 2
def baseEnd_6829134 : Nat := 3506628195961589215518391

theorem tailTrace_6829134 : CollatzResearch.WordTrace tailWord_6829134 prefixEnd_6829134 3506628195961589215518391 := by
  unfold tailWord_6829134
  simp only [CollatzResearch.WordTrace]
  refine ⟨31134872455152664509571807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166052653094147544051049637 31134872455152664509571807)
  ·
    refine ⟨46702308682728996764357711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31134872455152664509571807 46702308682728996764357711)
    ·
      refine ⟨70053463024093495146536567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46702308682728996764357711 70053463024093495146536567)
      ·
        refine ⟨105080194536140242719804851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70053463024093495146536567 105080194536140242719804851)
        ·
          refine ⟨157620291804210364079707277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105080194536140242719804851 157620291804210364079707277)
          ·
            refine ⟨59107609426578886529890229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157620291804210364079707277 59107609426578886529890229)
            ·
              refine ⟨5541338383741770612177209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59107609426578886529890229 5541338383741770612177209)
              ·
                refine ⟨4156003787806327959132907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5541338383741770612177209 4156003787806327959132907)
                ·
                  refine ⟨6234005681709491938699361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4156003787806327959132907 6234005681709491938699361)
                  ·
                    refine ⟨4675504261282118954024521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6234005681709491938699361 4675504261282118954024521)
                    ·
                      refine ⟨3506628195961589215518391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4675504261282118954024521 3506628195961589215518391)
                      ·
                        rfl

theorem cell23_6829134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2].length) (baseStart_6829134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829134 prefixEnd_6829134 := by exact prefixLift 6829134
  have htrace : WordTrace (prefixWord ++ tailWord_6829134) baseStart_6829134 baseEnd_6829134 := by
    simpa [prefixWord, tailWord_6829134, baseEnd_6829134] using wordTrace_append hprefix tailTrace_6829134
  have hstable : (prefixWord ++ tailWord_6829134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829134).length < 2 ^ (prefixWord ++ tailWord_6829134).sum := by decide
  have hdescent : baseEnd_6829134 < baseStart_6829134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829143 : List Nat := [1, 1, 3, 2, 2, 1, 1, 4, 3, 3, 2]
def baseStart_6829143 : Nat := 118140960795 + 6829143 * 2 ^ 59
def prefixEnd_6829143 : Nat := 4983230072969 + 3 ^ 40 * 6829143 * 2
def baseEnd_6829143 : Nat := 3506632817287479680305849

theorem tailTrace_6829143 : CollatzResearch.WordTrace tailWord_6829143 prefixEnd_6829143 3506632817287479680305849 := by
  unfold tailWord_6829143
  simp only [CollatzResearch.WordTrace]
  refine ⟨249079307898188710613652083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166052871932125807075768055 249079307898188710613652083)
  ·
    refine ⟨373618961847283065920478125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249079307898188710613652083 373618961847283065920478125)
    ·
      refine ⟨140107110692731149720179297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373618961847283065920478125 140107110692731149720179297)
      ·
        refine ⟨105080333019548362290134473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140107110692731149720179297 105080333019548362290134473)
        ·
          refine ⟨78810249764661271717600855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105080333019548362290134473 78810249764661271717600855)
          ·
            refine ⟨118215374646991907576401283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78810249764661271717600855 118215374646991907576401283)
            ·
              refine ⟨177323061970487861364601925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118215374646991907576401283 177323061970487861364601925)
              ·
                refine ⟨33248074119466474005862861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177323061970487861364601925 33248074119466474005862861)
                ·
                  refine ⟨12468027794799927752198573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33248074119466474005862861 12468027794799927752198573)
                  ·
                    refine ⟨4675510423049972907074465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12468027794799927752198573 4675510423049972907074465)
                    ·
                      refine ⟨3506632817287479680305849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4675510423049972907074465 3506632817287479680305849)
                      ·
                        rfl

theorem cell23_6829143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 3, 2].length) (baseStart_6829143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829143 prefixEnd_6829143 := by exact prefixLift 6829143
  have htrace : WordTrace (prefixWord ++ tailWord_6829143) baseStart_6829143 baseEnd_6829143 := by
    simpa [prefixWord, tailWord_6829143, baseEnd_6829143] using wordTrace_append hprefix tailTrace_6829143
  have hstable : (prefixWord ++ tailWord_6829143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829143).length < 2 ^ (prefixWord ++ tailWord_6829143).sum := by decide
  have hdescent : baseEnd_6829143 < baseStart_6829143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829176 : List Nat := [2, 1, 2, 1, 1, 1, 6, 1, 2, 1, 5]
def baseStart_6829176 : Nat := 118140960795 + 6829176 * 2 ^ 59
def prefixEnd_6829176 : Nat := 4983230072969 + 3 ^ 40 * 6829176 * 2
def baseEnd_6829176 : Nat := 3506649762149078051193197

theorem tailTrace_6829176 : CollatzResearch.WordTrace tailWord_6829176 prefixEnd_6829176 3506649762149078051193197 := by
  unfold tailWord_6829176
  simp only [CollatzResearch.WordTrace]
  refine ⟨124540255753534578624801691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166053674338046104833068921 124540255753534578624801691)
  ·
    refine ⟨186810383630301867937202537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124540255753534578624801691 186810383630301867937202537)
    ·
      refine ⟨140107787722726400952901903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186810383630301867937202537 140107787722726400952901903)
      ·
        refine ⟨210161681584089601429352855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140107787722726400952901903 210161681584089601429352855)
        ·
          refine ⟨315242522376134402144029283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210161681584089601429352855 315242522376134402144029283)
          ·
            refine ⟨472863783564201603216043925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315242522376134402144029283 472863783564201603216043925)
            ·
              refine ⟨22165489854571950150752059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 472863783564201603216043925 22165489854571950150752059)
              ·
                refine ⟨33248234781857925226128089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22165489854571950150752059 33248234781857925226128089)
                ·
                  refine ⟨24936176086393443919596067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33248234781857925226128089 24936176086393443919596067)
                  ·
                    refine ⟨37404264129590165879394101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24936176086393443919596067 37404264129590165879394101)
                    ·
                      refine ⟨3506649762149078051193197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37404264129590165879394101 3506649762149078051193197)
                      ·
                        rfl

theorem cell23_6829176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_6829176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829176 prefixEnd_6829176 := by exact prefixLift 6829176
  have htrace : WordTrace (prefixWord ++ tailWord_6829176) baseStart_6829176 baseEnd_6829176 := by
    simpa [prefixWord, tailWord_6829176, baseEnd_6829176] using wordTrace_append hprefix tailTrace_6829176
  have hstable : (prefixWord ++ tailWord_6829176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829176).length < 2 ^ (prefixWord ++ tailWord_6829176).sum := by decide
  have hdescent : baseEnd_6829176 < baseStart_6829176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829207 : List Nat := [1, 1, 3, 3, 3, 1, 2, 3, 2, 2, 2]
def baseStart_6829207 : Nat := 118140960795 + 6829207 * 2 ^ 59
def prefixEnd_6829207 : Nat := 4983230072969 + 3 ^ 40 * 6829207 * 2
def baseEnd_6829207 : Nat := 3506665680049367429905555

theorem tailTrace_6829207 : CollatzResearch.WordTrace tailWord_6829207 prefixEnd_6829207 3506665680049367429905555 := by
  unfold tailWord_6829207
  simp only [CollatzResearch.WordTrace]
  refine ⟨249081642169956849543981875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166054428113304566362654583 249081642169956849543981875)
  ·
    refine ⟨373622463254935274315972813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249081642169956849543981875 373622463254935274315972813)
    ·
      refine ⟨140108423720600727868489805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373622463254935274315972813 140108423720600727868489805)
      ·
        refine ⟨52540658895225272950683677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140108423720600727868489805 52540658895225272950683677)
        ·
          refine ⟨19702747085709477356506379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52540658895225272950683677 19702747085709477356506379)
          ·
            refine ⟨29554120628564216034759569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19702747085709477356506379 29554120628564216034759569)
            ·
              refine ⟨22165590471423162026069677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29554120628564216034759569 22165590471423162026069677)
              ·
                refine ⟨8312096426783685759776129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22165590471423162026069677 8312096426783685759776129)
                ·
                  refine ⟨6234072320087764319832097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8312096426783685759776129 6234072320087764319832097)
                  ·
                    refine ⟨4675554240065823239874073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6234072320087764319832097 4675554240065823239874073)
                    ·
                      refine ⟨3506665680049367429905555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4675554240065823239874073 3506665680049367429905555)
                      ·
                        rfl

theorem cell23_6829207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_6829207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829207 prefixEnd_6829207 := by exact prefixLift 6829207
  have htrace : WordTrace (prefixWord ++ tailWord_6829207) baseStart_6829207 baseEnd_6829207 := by
    simpa [prefixWord, tailWord_6829207, baseEnd_6829207] using wordTrace_append hprefix tailTrace_6829207
  have hstable : (prefixWord ++ tailWord_6829207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829207).length < 2 ^ (prefixWord ++ tailWord_6829207).sum := by decide
  have hdescent : baseEnd_6829207 < baseStart_6829207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829263 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 1, 6, 2]
def baseStart_6829263 : Nat := 118140960795 + 6829263 * 2 ^ 59
def prefixEnd_6829263 : Nat := 4983230072969 + 3 ^ 40 * 6829263 * 2
def baseEnd_6829263 : Nat := 3506694434966019210805297

theorem tailTrace_6829263 : CollatzResearch.WordTrace tailWord_6829263 prefixEnd_6829263 3506694434966019210805297 := by
  unfold tailWord_6829263
  simp only [CollatzResearch.WordTrace]
  refine ⟨249083684657753971108020443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166055789771835980738680295 249083684657753971108020443)
  ·
    refine ⟨373625526986630956662030665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249083684657753971108020443 373625526986630956662030665)
    ·
      refine ⟨280219145239973217496522999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373625526986630956662030665 280219145239973217496522999)
      ·
        refine ⟨420328717859959826244784499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280219145239973217496522999 420328717859959826244784499)
        ·
          refine ⟨630493076789939739367176749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420328717859959826244784499 630493076789939739367176749)
          ·
            refine ⟨236434903796227402262691281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 630493076789939739367176749 236434903796227402262691281)
            ·
              refine ⟨177326177847170551697018461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236434903796227402262691281 177326177847170551697018461)
              ·
                refine ⟨66497316692688956886381923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177326177847170551697018461 66497316692688956886381923)
                ·
                  refine ⟨99745975039033435329572885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66497316692688956886381923 99745975039033435329572885)
                  ·
                    refine ⟨4675592579954692281073729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 99745975039033435329572885 4675592579954692281073729)
                    ·
                      refine ⟨3506694434966019210805297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4675592579954692281073729 3506694434966019210805297)
                      ·
                        rfl

theorem cell23_6829263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 6, 2].length) (baseStart_6829263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829263 prefixEnd_6829263 := by exact prefixLift 6829263
  have htrace : WordTrace (prefixWord ++ tailWord_6829263) baseStart_6829263 baseEnd_6829263 := by
    simpa [prefixWord, tailWord_6829263, baseEnd_6829263] using wordTrace_append hprefix tailTrace_6829263
  have hstable : (prefixWord ++ tailWord_6829263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829263).length < 2 ^ (prefixWord ++ tailWord_6829263).sum := by decide
  have hdescent : baseEnd_6829263 < baseStart_6829263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829320 : List Nat := [2, 1, 3, 2, 4, 1, 1, 3, 6]
def baseStart_6829320 : Nat := 118140960795 + 6829320 * 2 ^ 59
def prefixEnd_6829320 : Nat := 4983230072969 + 3 ^ 40 * 6829320 * 2
def baseEnd_6829320 : Nat := 389635967040369498643615

theorem tailTrace_6829320 : CollatzResearch.WordTrace tailWord_6829320 prefixEnd_6829320 389635967040369498643615 := by
  unfold tailWord_6829320
  simp only [CollatzResearch.WordTrace]
  refine ⟨124542881809273734921422707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166057175745698313228563609 124542881809273734921422707)
  ·
    refine ⟨186814322713910602382134061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124542881809273734921422707 186814322713910602382134061)
    ·
      refine ⟨70055371017716475893300273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186814322713910602382134061 70055371017716475893300273)
      ·
        refine ⟨52541528263287356919975205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70055371017716475893300273 52541528263287356919975205)
        ·
          refine ⟨9851536549366379422495351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52541528263287356919975205 9851536549366379422495351)
          ·
            refine ⟨14777304824049569133743027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9851536549366379422495351 14777304824049569133743027)
            ·
              refine ⟨22165957236074353700614541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14777304824049569133743027 22165957236074353700614541)
              ·
                refine ⟨8312233963527882637730453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22165957236074353700614541 8312233963527882637730453)
                ·
                  refine ⟨389635967040369498643615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8312233963527882637730453 389635967040369498643615)
                  ·
                    rfl

theorem cell23_6829320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 6].length) (baseStart_6829320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829320 prefixEnd_6829320 := by exact prefixLift 6829320
  have htrace : WordTrace (prefixWord ++ tailWord_6829320) baseStart_6829320 baseEnd_6829320 := by
    simpa [prefixWord, tailWord_6829320, baseEnd_6829320] using wordTrace_append hprefix tailTrace_6829320
  have hstable : (prefixWord ++ tailWord_6829320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829320).length < 2 ^ (prefixWord ++ tailWord_6829320).sum := by decide
  have hdescent : baseEnd_6829320 < baseStart_6829320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829340 : List Nat := [2, 2, 3, 1, 1, 1, 2, 3, 1, 5, 2]
def baseStart_6829340 : Nat := 118140960795 + 6829340 * 2 ^ 59
def prefixEnd_6829340 : Nat := 4983230072969 + 3 ^ 40 * 6829340 * 2
def baseEnd_6829340 : Nat := 3506733972976415409542443

theorem tailTrace_6829340 : CollatzResearch.WordTrace tailWord_6829340 prefixEnd_6829340 3506733972976415409542443 := by
  unfold tailWord_6829340
  simp only [CollatzResearch.WordTrace]
  refine ⟨124543246539237506629286737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166057662052316675505715649 124543246539237506629286737)
  ·
    refine ⟨93407434904428129971965053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124543246539237506629286737 93407434904428129971965053)
    ·
      refine ⟨35027788089160548739486895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93407434904428129971965053 35027788089160548739486895)
      ·
        refine ⟨52541682133740823109230343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35027788089160548739486895 52541682133740823109230343)
        ·
          refine ⟨78812523200611234663845515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52541682133740823109230343 78812523200611234663845515)
          ·
            refine ⟨118218784800916851995768273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78812523200611234663845515 118218784800916851995768273)
            ·
              refine ⟨88664088600687638996826205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118218784800916851995768273 88664088600687638996826205)
              ·
                refine ⟨33249033225257864623809827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88664088600687638996826205 33249033225257864623809827)
                ·
                  refine ⟨49873549837886796935714741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33249033225257864623809827 49873549837886796935714741)
                  ·
                    refine ⟨4675645297301887212723257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49873549837886796935714741 4675645297301887212723257)
                    ·
                      refine ⟨3506733972976415409542443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4675645297301887212723257 3506733972976415409542443)
                      ·
                        rfl

theorem cell23_6829340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_6829340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829340 prefixEnd_6829340 := by exact prefixLift 6829340
  have htrace : WordTrace (prefixWord ++ tailWord_6829340) baseStart_6829340 baseEnd_6829340 := by
    simpa [prefixWord, tailWord_6829340, baseEnd_6829340] using wordTrace_append hprefix tailTrace_6829340
  have hstable : (prefixWord ++ tailWord_6829340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829340).length < 2 ^ (prefixWord ++ tailWord_6829340).sum := by decide
  have hdescent : baseEnd_6829340 < baseStart_6829340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829390 : List Nat := [4, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3]
def baseStart_6829390 : Nat := 118140960795 + 6829390 * 2 ^ 59
def prefixEnd_6829390 : Nat := 4983230072969 + 3 ^ 40 * 6829390 * 2
def baseEnd_6829390 : Nat := 3506759647009140213917213

theorem tailTrace_6829390 : CollatzResearch.WordTrace tailWord_6829390 prefixEnd_6829390 3506759647009140213917213 := by
  unfold tailWord_6829390
  simp only [CollatzResearch.WordTrace]
  refine ⟨31136039591036733974736703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166058877818862581198595749 31136039591036733974736703)
  ·
    refine ⟨46704059386555100962105055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31136039591036733974736703 46704059386555100962105055)
    ·
      refine ⟨70056089079832651443157583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46704059386555100962105055 70056089079832651443157583)
      ·
        refine ⟨105084133619748977164736375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70056089079832651443157583 105084133619748977164736375)
        ·
          refine ⟨157626200429623465747104563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105084133619748977164736375 157626200429623465747104563)
          ·
            refine ⟨236439300644435198620656845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157626200429623465747104563 236439300644435198620656845)
            ·
              refine ⟨88664737741663199482746317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236439300644435198620656845 88664737741663199482746317)
              ·
                refine ⟨33249276653123699806029869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88664737741663199482746317 33249276653123699806029869)
                ·
                  refine ⟨12468478744921387427261201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33249276653123699806029869 12468478744921387427261201)
                  ·
                    refine ⟨9351359058691040570445901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12468478744921387427261201 9351359058691040570445901)
                    ·
                      refine ⟨3506759647009140213917213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9351359058691040570445901 3506759647009140213917213)
                      ·
                        rfl

theorem cell23_6829390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_6829390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829390 prefixEnd_6829390 := by exact prefixLift 6829390
  have htrace : WordTrace (prefixWord ++ tailWord_6829390) baseStart_6829390 baseEnd_6829390 := by
    simpa [prefixWord, tailWord_6829390, baseEnd_6829390] using wordTrace_append hprefix tailTrace_6829390
  have hstable : (prefixWord ++ tailWord_6829390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829390).length < 2 ^ (prefixWord ++ tailWord_6829390).sum := by decide
  have hdescent : baseEnd_6829390 < baseStart_6829390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829421 : List Nat := [1, 5, 1, 1, 1, 3, 2, 4, 1, 2, 2]
def baseStart_6829421 : Nat := 118140960795 + 6829421 * 2 ^ 59
def prefixEnd_6829421 : Nat := 4983230072969 + 3 ^ 40 * 6829421 * 2
def baseEnd_6829421 : Nat := 3506775564909429592629571

theorem tailTrace_6829421 : CollatzResearch.WordTrace tailWord_6829421 prefixEnd_6829421 3506775564909429592629571 := by
  unfold tailWord_6829421
  simp only [CollatzResearch.WordTrace]
  refine ⟨249089447391181564092272117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166059631594121042728181411 249089447391181564092272117)
  ·
    refine ⟨23352135692923271633650511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 249089447391181564092272117 23352135692923271633650511)
    ·
      refine ⟨35028203539384907450475767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23352135692923271633650511 35028203539384907450475767)
      ·
        refine ⟨52542305309077361175713651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35028203539384907450475767 52542305309077361175713651)
        ·
          refine ⟨78813457963616041763570477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52542305309077361175713651 78813457963616041763570477)
          ·
            refine ⟨29555046736356015661338929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78813457963616041763570477 29555046736356015661338929)
            ·
              refine ⟨22166285052267011746004197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29555046736356015661338929 22166285052267011746004197)
              ·
                refine ⟨4156178447300064702375787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22166285052267011746004197 4156178447300064702375787)
                ·
                  refine ⟨6234267670950097053563681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4156178447300064702375787 6234267670950097053563681)
                  ·
                    refine ⟨4675700753212572790172761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6234267670950097053563681 4675700753212572790172761)
                    ·
                      refine ⟨3506775564909429592629571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4675700753212572790172761 3506775564909429592629571)
                      ·
                        rfl

theorem cell23_6829421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_6829421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829421 prefixEnd_6829421 := by exact prefixLift 6829421
  have htrace : WordTrace (prefixWord ++ tailWord_6829421) baseStart_6829421 baseEnd_6829421 := by
    simpa [prefixWord, tailWord_6829421, baseEnd_6829421] using wordTrace_append hprefix tailTrace_6829421
  have hstable : (prefixWord ++ tailWord_6829421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829421).length < 2 ^ (prefixWord ++ tailWord_6829421).sum := by decide
  have hdescent : baseEnd_6829421 < baseStart_6829421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829503 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 8]
def baseStart_6829503 : Nat := 118140960795 + 6829503 * 2 ^ 59
def prefixEnd_6829503 : Nat := 4983230072969 + 3 ^ 40 * 6829503 * 2
def baseEnd_6829503 : Nat := 3506817670323098271804193

theorem tailTrace_6829503 : CollatzResearch.WordTrace tailWord_6829503 prefixEnd_6829503 3506817670323098271804193 := by
  unfold tailWord_6829503
  simp only [CollatzResearch.WordTrace]
  refine ⟨249092438176884492096757163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166061625451256328064504775 249092438176884492096757163)
  ·
    refine ⟨373638657265326738145135745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249092438176884492096757163 373638657265326738145135745)
    ·
      refine ⟨280228992948995053608851809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373638657265326738145135745 280228992948995053608851809)
      ·
        refine ⟨210171744711746290206638857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280228992948995053608851809 210171744711746290206638857)
        ·
          refine ⟨157628808533809717654979143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210171744711746290206638857 157628808533809717654979143)
          ·
            refine ⟨236443212800714576482468715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157628808533809717654979143 236443212800714576482468715)
            ·
              refine ⟨354664819201071864723703073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236443212800714576482468715 354664819201071864723703073)
              ·
                refine ⟨265998614400803898542777305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354664819201071864723703073 265998614400803898542777305)
                ·
                  refine ⟨199498960800602923907082979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265998614400803898542777305 199498960800602923907082979)
                  ·
                    refine ⟨299248441200904385860624469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 199498960800602923907082979 299248441200904385860624469)
                    ·
                      refine ⟨3506817670323098271804193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 299248441200904385860624469 3506817670323098271804193)
                      ·
                        rfl

theorem cell23_6829503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_6829503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829503 prefixEnd_6829503 := by exact prefixLift 6829503
  have htrace : WordTrace (prefixWord ++ tailWord_6829503) baseStart_6829503 baseEnd_6829503 := by
    simpa [prefixWord, tailWord_6829503, baseEnd_6829503] using wordTrace_append hprefix tailTrace_6829503
  have hstable : (prefixWord ++ tailWord_6829503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829503).length < 2 ^ (prefixWord ++ tailWord_6829503).sum := by decide
  have hdescent : baseEnd_6829503 < baseStart_6829503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829523 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 7]
def baseStart_6829523 : Nat := 118140960795 + 6829523 * 2 ^ 59
def prefixEnd_6829523 : Nat := 4983230072969 + 3 ^ 40 * 6829523 * 2
def baseEnd_6829523 : Nat := 3506827939936188193554101

theorem tailTrace_6829523 : CollatzResearch.WordTrace tailWord_6829523 prefixEnd_6829523 3506827939936188193554101 := by
  unfold tailWord_6829523
  simp only [CollatzResearch.WordTrace]
  refine ⟨249093167636812035512485223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166062111757874690341656815 249093167636812035512485223)
  ·
    refine ⟨373639751455218053268727835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249093167636812035512485223 373639751455218053268727835)
    ·
      refine ⟨560459627182827079903091753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373639751455218053268727835 560459627182827079903091753)
      ·
        refine ⟨420344720387120309927318815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 560459627182827079903091753 420344720387120309927318815)
        ·
          refine ⟨630517080580680464890978223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420344720387120309927318815 630517080580680464890978223)
          ·
            refine ⟨945775620871020697336467335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630517080580680464890978223 945775620871020697336467335)
            ·
              refine ⟨1418663431306531046004701003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945775620871020697336467335 1418663431306531046004701003)
              ·
                refine ⟨2127995146959796569007051505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1418663431306531046004701003 2127995146959796569007051505)
                ·
                  refine ⟨1595996360219847426755288629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2127995146959796569007051505 1595996360219847426755288629)
                  ·
                    refine ⟨149624658770610696258308309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1595996360219847426755288629 149624658770610696258308309)
                    ·
                      refine ⟨3506827939936188193554101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149624658770610696258308309 3506827939936188193554101)
                      ·
                        rfl

theorem cell23_6829523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 7].length) (baseStart_6829523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829523 prefixEnd_6829523 := by exact prefixLift 6829523
  have htrace : WordTrace (prefixWord ++ tailWord_6829523) baseStart_6829523 baseEnd_6829523 := by
    simpa [prefixWord, tailWord_6829523, baseEnd_6829523] using wordTrace_append hprefix tailTrace_6829523
  have hstable : (prefixWord ++ tailWord_6829523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829523).length < 2 ^ (prefixWord ++ tailWord_6829523).sum := by decide
  have hdescent : baseEnd_6829523 < baseStart_6829523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829537 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 2, 5, 2]
def baseStart_6829537 : Nat := 118140960795 + 6829537 * 2 ^ 59
def prefixEnd_6829537 : Nat := 4983230072969 + 3 ^ 40 * 6829537 * 2
def baseEnd_6829537 : Nat := 3506835128665351138779037

theorem tailTrace_6829537 : CollatzResearch.WordTrace tailWord_6829537 prefixEnd_6829537 3506835128665351138779037 := by
  unfold tailWord_6829537
  simp only [CollatzResearch.WordTrace]
  refine ⟨249093678258761315903494865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166062452172507543935663243 249093678258761315903494865)
  ·
    refine ⟨186820258694070986927621149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249093678258761315903494865 186820258694070986927621149)
    ·
      refine ⟨70057597010276620097857931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186820258694070986927621149 70057597010276620097857931)
      ·
        refine ⟨105086395515414930146786897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70057597010276620097857931 105086395515414930146786897)
        ·
          refine ⟨78814796636561197610090173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105086395515414930146786897 78814796636561197610090173)
          ·
            refine ⟨29555548738710449103783815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78814796636561197610090173 29555548738710449103783815)
            ·
              refine ⟨44333323108065673655675723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29555548738710449103783815 44333323108065673655675723)
              ·
                refine ⟨66499984662098510483513585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44333323108065673655675723 66499984662098510483513585)
                ·
                  refine ⟨49874988496573882862635189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66499984662098510483513585 49874988496573882862635189)
                  ·
                    refine ⟨4675780171553801518372049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49874988496573882862635189 4675780171553801518372049)
                    ·
                      refine ⟨3506835128665351138779037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4675780171553801518372049 3506835128665351138779037)
                      ·
                        rfl

theorem cell23_6829537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 5, 2].length) (baseStart_6829537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829537 prefixEnd_6829537 := by exact prefixLift 6829537
  have htrace : WordTrace (prefixWord ++ tailWord_6829537) baseStart_6829537 baseEnd_6829537 := by
    simpa [prefixWord, tailWord_6829537, baseEnd_6829537] using wordTrace_append hprefix tailTrace_6829537
  have hstable : (prefixWord ++ tailWord_6829537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829537).length < 2 ^ (prefixWord ++ tailWord_6829537).sum := by decide
  have hdescent : baseEnd_6829537 < baseStart_6829537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829628 : List Nat := [2, 2, 2, 2, 4, 2, 1, 3, 1, 4]
def baseStart_6829628 : Nat := 118140960795 + 6829628 * 2 ^ 59
def prefixEnd_6829628 : Nat := 4983230072969 + 3 ^ 40 * 6829628 * 2
def baseEnd_6829628 : Nat := 1168960618468303427580373

theorem tailTrace_6829628 : CollatzResearch.WordTrace tailWord_6829628 prefixEnd_6829628 1168960618468303427580373 := by
  unfold tailWord_6829628
  simp only [CollatzResearch.WordTrace]
  refine ⟨124548498650715819222528769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166064664867621092296705025 124548498650715819222528769)
  ·
    refine ⟨93411373988036864416896577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124548498650715819222528769 93411373988036864416896577)
    ·
      refine ⟨70058530491027648312672433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93411373988036864416896577 70058530491027648312672433)
      ·
        refine ⟨52543897868270736234504325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70058530491027648312672433 52543897868270736234504325)
        ·
          refine ⟨9851980850300763043969561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52543897868270736234504325 9851980850300763043969561)
          ·
            refine ⟨7388985637725572282977171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9851980850300763043969561 7388985637725572282977171)
            ·
              refine ⟨11083478456588358424465757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7388985637725572282977171 11083478456588358424465757)
              ·
                refine ⟨4156304421220634409174659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11083478456588358424465757 4156304421220634409174659)
                ·
                  refine ⟨6234456631830951613761989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4156304421220634409174659 6234456631830951613761989)
                  ·
                    refine ⟨1168960618468303427580373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6234456631830951613761989 1168960618468303427580373)
                    ·
                      rfl

theorem cell23_6829628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_6829628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829628 prefixEnd_6829628 := by exact prefixLift 6829628
  have htrace : WordTrace (prefixWord ++ tailWord_6829628) baseStart_6829628 baseEnd_6829628 := by
    simpa [prefixWord, tailWord_6829628, baseEnd_6829628] using wordTrace_append hprefix tailTrace_6829628
  have hstable : (prefixWord ++ tailWord_6829628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829628).length < 2 ^ (prefixWord ++ tailWord_6829628).sum := by decide
  have hdescent : baseEnd_6829628 < baseStart_6829628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829637 : List Nat := [1, 3, 1, 1, 1, 4, 1, 5, 1, 5]
def baseStart_6829637 : Nat := 118140960795 + 6829637 * 2 ^ 59
def prefixEnd_6829637 : Nat := 4983230072969 + 3 ^ 40 * 6829637 * 2
def baseEnd_6829637 : Nat := 1168962158910266915842859

theorem tailTrace_6829637 : CollatzResearch.WordTrace tailWord_6829637 prefixEnd_6829637 1168962158910266915842859 := by
  unfold tailWord_6829637
  simp only [CollatzResearch.WordTrace]
  refine ⟨249097325558399032982135165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166064883705599355321423443 249097325558399032982135165)
  ·
    refine ⟨93411497084399637368300687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249097325558399032982135165 93411497084399637368300687)
    ·
      refine ⟨140117245626599456052451031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93411497084399637368300687 140117245626599456052451031)
      ·
        refine ⟨210175868439899184078676547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140117245626599456052451031 210175868439899184078676547)
        ·
          refine ⟨315263802659848776118014821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210175868439899184078676547 315263802659848776118014821)
          ·
            refine ⟨59111962998721645522127779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 315263802659848776118014821 59111962998721645522127779)
            ·
              refine ⟨88667944498082468283191669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59111962998721645522127779 88667944498082468283191669)
              ·
                refine ⟨8312619796695231401549219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88667944498082468283191669 8312619796695231401549219)
                ·
                  refine ⟨12468929695042847102323829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8312619796695231401549219 12468929695042847102323829)
                  ·
                    refine ⟨1168962158910266915842859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12468929695042847102323829 1168962158910266915842859)
                    ·
                      rfl

theorem cell23_6829637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 5].length) (baseStart_6829637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829637 prefixEnd_6829637 := by exact prefixLift 6829637
  have htrace : WordTrace (prefixWord ++ tailWord_6829637) baseStart_6829637 baseEnd_6829637 := by
    simpa [prefixWord, tailWord_6829637, baseEnd_6829637] using wordTrace_append hprefix tailTrace_6829637
  have hstable : (prefixWord ++ tailWord_6829637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829637).length < 2 ^ (prefixWord ++ tailWord_6829637).sum := by decide
  have hdescent : baseEnd_6829637 < baseStart_6829637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829638 : List Nat := [6, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3]
def baseStart_6829638 : Nat := 118140960795 + 6829638 * 2 ^ 59
def prefixEnd_6829638 : Nat := 4983230072969 + 3 ^ 40 * 6829638 * 2
def baseEnd_6829638 : Nat := 3506886990211455243616073

theorem tailTrace_6829638 : CollatzResearch.WordTrace tailWord_6829638 prefixEnd_6829638 3506886990211455243616073 := by
  unfold tailWord_6829638
  simp only [CollatzResearch.WordTrace]
  refine ⟨7784292563481106567278799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 166064908020930273435281045 7784292563481106567278799)
  ·
    refine ⟨11676438845221659850918199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7784292563481106567278799 11676438845221659850918199)
    ·
      refine ⟨17514658267832489776377299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11676438845221659850918199 17514658267832489776377299)
      ·
        refine ⟨26271987401748734664565949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17514658267832489776377299 26271987401748734664565949)
        ·
          refine ⟨9851995275655775499212231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26271987401748734664565949 9851995275655775499212231)
          ·
            refine ⟨14777992913483663248818347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9851995275655775499212231 14777992913483663248818347)
            ·
              refine ⟨22166989370225494873227521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14777992913483663248818347 22166989370225494873227521)
              ·
                refine ⟨16625242027669121154920641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22166989370225494873227521 16625242027669121154920641)
                ·
                  refine ⟨12468931520751840866190481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16625242027669121154920641 12468931520751840866190481)
                  ·
                    refine ⟨9351698640563880649642861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12468931520751840866190481 9351698640563880649642861)
                    ·
                      refine ⟨3506886990211455243616073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9351698640563880649642861 3506886990211455243616073)
                      ·
                        rfl

theorem cell23_6829638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_6829638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829638 prefixEnd_6829638 := by exact prefixLift 6829638
  have htrace : WordTrace (prefixWord ++ tailWord_6829638) baseStart_6829638 baseEnd_6829638 := by
    simpa [prefixWord, tailWord_6829638, baseEnd_6829638] using wordTrace_append hprefix tailTrace_6829638
  have hstable : (prefixWord ++ tailWord_6829638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829638).length < 2 ^ (prefixWord ++ tailWord_6829638).sum := by decide
  have hdescent : baseEnd_6829638 < baseStart_6829638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829644 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 4, 3, 2]
def baseStart_6829644 : Nat := 118140960795 + 6829644 * 2 ^ 59
def prefixEnd_6829644 : Nat := 4983230072969 + 3 ^ 40 * 6829644 * 2
def baseEnd_6829644 : Nat := 3506890071095382220141045

theorem tailTrace_6829644 : CollatzResearch.WordTrace tailWord_6829644 prefixEnd_6829644 3506890071095382220141045 := by
  unfold tailWord_6829644
  simp only [CollatzResearch.WordTrace]
  refine ⟨124548790434686836588819993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166065053912915782118426657 124548790434686836588819993)
  ·
    refine ⟨93411592826015127441614995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124548790434686836588819993 93411592826015127441614995)
    ·
      refine ⟨140117389239022691162422493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93411592826015127441614995 140117389239022691162422493)
      ·
        refine ⟨52544020964633509185908435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140117389239022691162422493 52544020964633509185908435)
        ·
          refine ⟨78816031446950263778862653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52544020964633509185908435 78816031446950263778862653)
          ·
            refine ⟨29556011792606348917073495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78816031446950263778862653 29556011792606348917073495)
            ·
              refine ⟨44334017688909523375610243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29556011792606348917073495 44334017688909523375610243)
              ·
                refine ⟨66501026533364285063415365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44334017688909523375610243 66501026533364285063415365)
                ·
                  refine ⟨12468942475005803449390381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66501026533364285063415365 12468942475005803449390381)
                  ·
                    refine ⟨4675853428127176293521393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12468942475005803449390381 4675853428127176293521393)
                    ·
                      refine ⟨3506890071095382220141045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4675853428127176293521393 3506890071095382220141045)
                      ·
                        rfl

theorem cell23_6829644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_6829644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829644 prefixEnd_6829644 := by exact prefixLift 6829644
  have htrace : WordTrace (prefixWord ++ tailWord_6829644) baseStart_6829644 baseEnd_6829644 := by
    simpa [prefixWord, tailWord_6829644, baseEnd_6829644] using wordTrace_append hprefix tailTrace_6829644
  have hstable : (prefixWord ++ tailWord_6829644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829644).length < 2 ^ (prefixWord ++ tailWord_6829644).sum := by decide
  have hdescent : baseEnd_6829644 < baseStart_6829644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829645 : List Nat := [1, 6, 1, 1, 3, 1, 3, 2, 1, 4]
def baseStart_6829645 : Nat := 118140960795 + 6829645 * 2 ^ 59
def prefixEnd_6829645 : Nat := 4983230072969 + 3 ^ 40 * 6829645 * 2
def baseEnd_6829645 : Nat := 1168963528192012238742847

theorem tailTrace_6829645 : CollatzResearch.WordTrace tailWord_6829645 prefixEnd_6829645 1168963528192012238742847 := by
  unfold tailWord_6829645
  simp only [CollatzResearch.WordTrace]
  refine ⟨249097617342370050348426389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166065078228246700232284259 249097617342370050348426389)
  ·
    refine ⟨11676450812923596110082487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 249097617342370050348426389 11676450812923596110082487)
    ·
      refine ⟨17514676219385394165123731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11676450812923596110082487 17514676219385394165123731)
      ·
        refine ⟨26272014329078091247685597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17514676219385394165123731 26272014329078091247685597)
        ·
          refine ⟨9852005373404284217882099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26272014329078091247685597 9852005373404284217882099)
          ·
            refine ⟨14778008060106426326823149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9852005373404284217882099 14778008060106426326823149)
            ·
              refine ⟨5541753022539909872558681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14778008060106426326823149 5541753022539909872558681)
              ·
                refine ⟨4156314766904932404419011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5541753022539909872558681 4156314766904932404419011)
                ·
                  refine ⟨6234472150357398606628517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4156314766904932404419011 6234472150357398606628517)
                  ·
                    refine ⟨1168963528192012238742847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6234472150357398606628517 1168963528192012238742847)
                    ·
                      rfl

theorem cell23_6829645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_6829645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829645 prefixEnd_6829645 := by exact prefixLift 6829645
  have htrace : WordTrace (prefixWord ++ tailWord_6829645) baseStart_6829645 baseEnd_6829645 := by
    simpa [prefixWord, tailWord_6829645, baseEnd_6829645] using wordTrace_append hprefix tailTrace_6829645
  have hstable : (prefixWord ++ tailWord_6829645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829645).length < 2 ^ (prefixWord ++ tailWord_6829645).sum := by decide
  have hdescent : baseEnd_6829645 < baseStart_6829645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
