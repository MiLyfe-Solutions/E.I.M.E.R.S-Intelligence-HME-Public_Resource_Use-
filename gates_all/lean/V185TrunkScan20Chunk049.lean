import V185TrunkScan20Chunk048

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_298221 : List Nat := [1, 5, 1, 2, 2, 1, 4, 2, 2]
def baseStart_298221 : Nat := 118140960795 + 298221 * 2 ^ 59
def prefixEnd_298221 : Nat := 4983230072969 + 3 ^ 40 * 298221 * 2
def baseEnd_298221 : Nat := 136116190457407060147567

theorem tailTrace_298221 : CollatzResearch.WordTrace tailWord_298221 prefixEnd_298221 136116190457407060147567 := by
  unfold tailWord_298221
  simp only [CollatzResearch.WordTrace]
  refine ⟨10877013452603723936998517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7251342301735815957999011 10877013452603723936998517)
  ·
    refine ⟨1019720011181599119093611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10877013452603723936998517 1019720011181599119093611)
    ·
      refine ⟨1529580016772398678640417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1019720011181599119093611 1529580016772398678640417)
      ·
        refine ⟨1147185012579299008980313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1529580016772398678640417 1147185012579299008980313)
        ·
          refine ⟨860388759434474256735235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1147185012579299008980313 860388759434474256735235)
          ·
            refine ⟨1290583139151711385102853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 860388759434474256735235 1290583139151711385102853)
            ·
              refine ⟨241984338590945884706785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1290583139151711385102853 241984338590945884706785)
              ·
                refine ⟨181488253943209413530089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 241984338590945884706785 181488253943209413530089)
                ·
                  refine ⟨136116190457407060147567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 181488253943209413530089 136116190457407060147567)
                  ·
                    rfl

theorem cell20_298221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_298221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298221 prefixEnd_298221 := by exact prefixLift 298221
  have htrace : WordTrace (prefixWord ++ tailWord_298221) baseStart_298221 baseEnd_298221 := by
    simpa [prefixWord, tailWord_298221, baseEnd_298221] using wordTrace_append hprefix tailTrace_298221
  have hstable : (prefixWord ++ tailWord_298221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298221).length < 2 ^ (prefixWord ++ tailWord_298221).sum := by decide
  have hdescent : baseEnd_298221 < baseStart_298221 := by decide
  rcases family_descends (prefixWord ++ tailWord_298221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298239 : List Nat := [1, 1, 2, 2, 1, 5, 2, 3, 3]
def baseStart_298239 : Nat := 118140960795 + 298239 * 2 ^ 59
def prefixEnd_298239 : Nat := 4983230072969 + 3 ^ 40 * 298239 * 2
def baseEnd_298239 : Nat := 136124406147878997547493

theorem tailTrace_298239 : CollatzResearch.WordTrace tailWord_298239 prefixEnd_298239 136124406147878997547493 := by
  unfold tailWord_298239
  simp only [CollatzResearch.WordTrace]
  refine ⟨10877669966538513011153771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7251779977692342007435847 10877669966538513011153771)
  ·
    refine ⟨16316504949807769516730657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10877669966538513011153771 16316504949807769516730657)
    ·
      refine ⟨12237378712355827137547993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16316504949807769516730657 12237378712355827137547993)
      ·
        refine ⟨9178034034266870353160995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12237378712355827137547993 9178034034266870353160995)
        ·
          refine ⟨13767051051400305529741493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9178034034266870353160995 13767051051400305529741493)
          ·
            refine ⟨1290661036068778643413265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13767051051400305529741493 1290661036068778643413265)
            ·
              refine ⟨967995777051583982559949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1290661036068778643413265 967995777051583982559949)
              ·
                refine ⟨362998416394343993459981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 967995777051583982559949 362998416394343993459981)
                ·
                  refine ⟨136124406147878997547493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 362998416394343993459981 136124406147878997547493)
                  ·
                    rfl

theorem cell20_298239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 3].length) (baseStart_298239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298239 prefixEnd_298239 := by exact prefixLift 298239
  have htrace : WordTrace (prefixWord ++ tailWord_298239) baseStart_298239 baseEnd_298239 := by
    simpa [prefixWord, tailWord_298239, baseEnd_298239] using wordTrace_append hprefix tailTrace_298239
  have hstable : (prefixWord ++ tailWord_298239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298239).length < 2 ^ (prefixWord ++ tailWord_298239).sum := by decide
  have hdescent : baseEnd_298239 < baseStart_298239 := by decide
  rcases family_descends (prefixWord ++ tailWord_298239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298242 : List Nat := [3, 4, 1, 1, 3, 1, 1, 2, 4]
def baseStart_298242 : Nat := 118140960795 + 298242 * 2 ^ 59
def prefixEnd_298242 : Nat := 4983230072969 + 3 ^ 40 * 298242 * 2
def baseEnd_298242 : Nat := 136125775429624320447481

theorem tailTrace_298242 : CollatzResearch.WordTrace tailWord_298242 prefixEnd_298242 136125775429624320447481 := by
  unfold tailWord_298242
  simp only [CollatzResearch.WordTrace]
  refine ⟨2719444846381911130878245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7251852923685096349008653 2719444846381911130878245)
  ·
    refine ⟨509895908696608337039671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2719444846381911130878245 509895908696608337039671)
    ·
      refine ⟨764843863044912505559507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 509895908696608337039671 764843863044912505559507)
      ·
        refine ⟨1147265794567368758339261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 764843863044912505559507 1147265794567368758339261)
        ·
          refine ⟨430224672962763284377223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1147265794567368758339261 430224672962763284377223)
          ·
            refine ⟨645337009444144926565835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 430224672962763284377223 645337009444144926565835)
            ·
              refine ⟨968005514166217389848753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 645337009444144926565835 968005514166217389848753)
              ·
                refine ⟨726004135624663042386565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 968005514166217389848753 726004135624663042386565)
                ·
                  refine ⟨136125775429624320447481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 726004135624663042386565 136125775429624320447481)
                  ·
                    rfl

theorem cell20_298242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_298242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298242 prefixEnd_298242 := by exact prefixLift 298242
  have htrace : WordTrace (prefixWord ++ tailWord_298242) baseStart_298242 baseEnd_298242 := by
    simpa [prefixWord, tailWord_298242, baseEnd_298242] using wordTrace_append hprefix tailTrace_298242
  have hstable : (prefixWord ++ tailWord_298242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298242).length < 2 ^ (prefixWord ++ tailWord_298242).sum := by decide
  have hdescent : baseEnd_298242 < baseStart_298242 := by decide
  rcases family_descends (prefixWord ++ tailWord_298242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298267 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 8]
def baseStart_298267 : Nat := 118140960795 + 298267 * 2 ^ 59
def prefixEnd_298267 : Nat := 4983230072969 + 3 ^ 40 * 298267 * 2
def baseEnd_298267 : Nat := 136137186110835344614045

theorem tailTrace_298267 : CollatzResearch.WordTrace tailWord_298267 prefixEnd_298267 136137186110835344614045 := by
  unfold tailWord_298267
  simp only [CollatzResearch.WordTrace]
  refine ⟨10878691210437073793173055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7252460806958049195448703 10878691210437073793173055)
  ·
    refine ⟨16318036815655610689759583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10878691210437073793173055 16318036815655610689759583)
    ·
      refine ⟨24477055223483416034639375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16318036815655610689759583 24477055223483416034639375)
      ·
        refine ⟨36715582835225124051959063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24477055223483416034639375 36715582835225124051959063)
        ·
          refine ⟨55073374252837686077938595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36715582835225124051959063 55073374252837686077938595)
          ·
            refine ⟨82610061379256529116907893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55073374252837686077938595 82610061379256529116907893)
            ·
              refine ⟨7744693254305299604710115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82610061379256529116907893 7744693254305299604710115)
              ·
                refine ⟨11617039881457949407065173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7744693254305299604710115 11617039881457949407065173)
                ·
                  refine ⟨136137186110835344614045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11617039881457949407065173 136137186110835344614045)
                  ·
                    rfl

theorem cell20_298267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 8].length) (baseStart_298267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298267 prefixEnd_298267 := by exact prefixLift 298267
  have htrace : WordTrace (prefixWord ++ tailWord_298267) baseStart_298267 baseEnd_298267 := by
    simpa [prefixWord, tailWord_298267, baseEnd_298267] using wordTrace_append hprefix tailTrace_298267
  have hstable : (prefixWord ++ tailWord_298267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298267).length < 2 ^ (prefixWord ++ tailWord_298267).sum := by decide
  have hdescent : baseEnd_298267 < baseStart_298267 := by decide
  rcases family_descends (prefixWord ++ tailWord_298267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298277 : List Nat := [1, 3, 1, 2, 4, 2, 1, 1, 5]
def baseStart_298277 : Nat := 118140960795 + 298277 * 2 ^ 59
def prefixEnd_298277 : Nat := 4983230072969 + 3 ^ 40 * 298277 * 2
def baseEnd_298277 : Nat := 136141750383319754280671

theorem tailTrace_298277 : CollatzResearch.WordTrace tailWord_298277 prefixEnd_298277 136141750383319754280671 := by
  unfold tailWord_298277
  simp only [CollatzResearch.WordTrace]
  refine ⟨10879055940400845501037085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7252703960267230334024723 10879055940400845501037085)
  ·
    refine ⟨4079645977650317062888907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10879055940400845501037085 4079645977650317062888907)
    ·
      refine ⟨6119468966475475594333361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4079645977650317062888907 6119468966475475594333361)
      ·
        refine ⟨4589601724856606695750021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6119468966475475594333361 4589601724856606695750021)
        ·
          refine ⟨860550323410613755453129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4589601724856606695750021 860550323410613755453129)
          ·
            refine ⟨645412742557960316589847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 860550323410613755453129 645412742557960316589847)
            ·
              refine ⟨968119113836940474884771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 645412742557960316589847 968119113836940474884771)
              ·
                refine ⟨1452178670755410712327157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 968119113836940474884771 1452178670755410712327157)
                ·
                  refine ⟨136141750383319754280671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1452178670755410712327157 136141750383319754280671)
                  ·
                    rfl

theorem cell20_298277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_298277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298277 prefixEnd_298277 := by exact prefixLift 298277
  have htrace : WordTrace (prefixWord ++ tailWord_298277) baseStart_298277 baseEnd_298277 := by
    simpa [prefixWord, tailWord_298277, baseEnd_298277] using wordTrace_append hprefix tailTrace_298277
  have hstable : (prefixWord ++ tailWord_298277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298277).length < 2 ^ (prefixWord ++ tailWord_298277).sum := by decide
  have hdescent : baseEnd_298277 < baseStart_298277 := by decide
  rcases family_descends (prefixWord ++ tailWord_298277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298280 : List Nat := [2, 1, 5, 1, 2, 1, 2, 4, 2]
def baseStart_298280 : Nat := 118140960795 + 298280 * 2 ^ 59
def prefixEnd_298280 : Nat := 4983230072969 + 3 ^ 40 * 298280 * 2
def baseEnd_298280 : Nat := 136143119665065077180659

theorem tailTrace_298280 : CollatzResearch.WordTrace tailWord_298280 prefixEnd_298280 136143119665065077180659 := by
  unfold tailWord_298280
  simp only [CollatzResearch.WordTrace]
  refine ⟨5439582679694988506698147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7252776906259984675597529 5439582679694988506698147)
  ·
    refine ⟨8159374019542482760047221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5439582679694988506698147 8159374019542482760047221)
    ·
      refine ⟨764941314332107758754427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8159374019542482760047221 764941314332107758754427)
      ·
        refine ⟨1147411971498161638131641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 764941314332107758754427 1147411971498161638131641)
        ·
          refine ⟨860558978623621228598731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1147411971498161638131641 860558978623621228598731)
          ·
            refine ⟨1290838467935431842898097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 860558978623621228598731 1290838467935431842898097)
            ·
              refine ⟨968128850951573882173573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1290838467935431842898097 968128850951573882173573)
              ·
                refine ⟨181524159553420102907545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 968128850951573882173573 181524159553420102907545)
                ·
                  refine ⟨136143119665065077180659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 181524159553420102907545 136143119665065077180659)
                  ·
                    rfl

theorem cell20_298280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 4, 2].length) (baseStart_298280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298280 prefixEnd_298280 := by exact prefixLift 298280
  have htrace : WordTrace (prefixWord ++ tailWord_298280) baseStart_298280 baseEnd_298280 := by
    simpa [prefixWord, tailWord_298280, baseEnd_298280] using wordTrace_append hprefix tailTrace_298280
  have hstable : (prefixWord ++ tailWord_298280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298280).length < 2 ^ (prefixWord ++ tailWord_298280).sum := by decide
  have hdescent : baseEnd_298280 < baseStart_298280 := by decide
  rcases family_descends (prefixWord ++ tailWord_298280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298310 : List Nat := [6, 1, 1, 3, 2, 1, 1, 3, 2]
def baseStart_298310 : Nat := 118140960795 + 298310 * 2 ^ 59
def prefixEnd_298310 : Nat := 4983230072969 + 3 ^ 40 * 298310 * 2
def baseEnd_298310 : Nat := 136156812482518306180537

theorem tailTrace_298310 : CollatzResearch.WordTrace tailWord_298310 prefixEnd_298310 136156812482518306180537 := by
  unfold tailWord_298310
  simp only [CollatzResearch.WordTrace]
  refine ⟨340008110915040379280887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7253506366187528091325589 340008110915040379280887)
  ·
    refine ⟨510012166372560568921331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 340008110915040379280887 510012166372560568921331)
    ·
      refine ⟨765018249558840853381997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 510012166372560568921331 765018249558840853381997)
      ·
        refine ⟨286881843584565320018249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 765018249558840853381997 286881843584565320018249)
        ·
          refine ⟨215161382688423990013687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286881843584565320018249 215161382688423990013687)
          ·
            refine ⟨322742074032635985020531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215161382688423990013687 322742074032635985020531)
            ·
              refine ⟨484113111048953977530797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322742074032635985020531 484113111048953977530797)
              ·
                refine ⟨181542416643357741574049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 484113111048953977530797 181542416643357741574049)
                ·
                  refine ⟨136156812482518306180537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 181542416643357741574049 136156812482518306180537)
                  ·
                    rfl

theorem cell20_298310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_298310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298310 prefixEnd_298310 := by exact prefixLift 298310
  have htrace : WordTrace (prefixWord ++ tailWord_298310) baseStart_298310 baseEnd_298310 := by
    simpa [prefixWord, tailWord_298310, baseEnd_298310] using wordTrace_append hprefix tailTrace_298310
  have hstable : (prefixWord ++ tailWord_298310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298310).length < 2 ^ (prefixWord ++ tailWord_298310).sum := by decide
  have hdescent : baseEnd_298310 < baseStart_298310 := by decide
  rcases family_descends (prefixWord ++ tailWord_298310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298339 : List Nat := [1, 1, 1, 5, 2, 4, 1, 1, 4]
def baseStart_298339 : Nat := 118140960795 + 298339 * 2 ^ 59
def prefixEnd_298339 : Nat := 4983230072969 + 3 ^ 40 * 298339 * 2
def baseEnd_298339 : Nat := 136170048872723094213751

theorem tailTrace_298339 : CollatzResearch.WordTrace tailWord_298339 prefixEnd_298339 136170048872723094213751 := by
  unfold tailWord_298339
  simp only [CollatzResearch.WordTrace]
  refine ⟨10881317266176230089794071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7254211510784153393196047 10881317266176230089794071)
  ·
    refine ⟨16321975899264345134691107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10881317266176230089794071 16321975899264345134691107)
    ·
      refine ⟨24482963848896517702036661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16321975899264345134691107 24482963848896517702036661)
      ·
        refine ⟨2295277860834048534565937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24482963848896517702036661 2295277860834048534565937)
        ·
          refine ⟨1721458395625536400924453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2295277860834048534565937 1721458395625536400924453)
          ·
            refine ⟨322773449179788075173335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1721458395625536400924453 322773449179788075173335)
            ·
              refine ⟨484160173769682112760003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322773449179788075173335 484160173769682112760003)
              ·
                refine ⟨726240260654523169140005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 484160173769682112760003 726240260654523169140005)
                ·
                  refine ⟨136170048872723094213751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 726240260654523169140005 136170048872723094213751)
                  ·
                    rfl

theorem cell20_298339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 4].length) (baseStart_298339 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298339 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298339 prefixEnd_298339 := by exact prefixLift 298339
  have htrace : WordTrace (prefixWord ++ tailWord_298339) baseStart_298339 baseEnd_298339 := by
    simpa [prefixWord, tailWord_298339, baseEnd_298339] using wordTrace_append hprefix tailTrace_298339
  have hstable : (prefixWord ++ tailWord_298339).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298339).length < 2 ^ (prefixWord ++ tailWord_298339).sum := by decide
  have hdescent : baseEnd_298339 < baseStart_298339 := by decide
  rcases family_descends (prefixWord ++ tailWord_298339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298349 : List Nat := [1, 5, 1, 1, 1, 5, 2, 1, 3]
def baseStart_298349 : Nat := 118140960795 + 298349 * 2 ^ 59
def prefixEnd_298349 : Nat := 4983230072969 + 3 ^ 40 * 298349 * 2
def baseEnd_298349 : Nat := 136174613145207503880377

theorem tailTrace_298349 : CollatzResearch.WordTrace tailWord_298349 prefixEnd_298349 136174613145207503880377 := by
  unfold tailWord_298349
  simp only [CollatzResearch.WordTrace]
  refine ⟨10881681996140001797658101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7254454664093334531772067 10881681996140001797658101)
  ·
    refine ⟨1020157687138125168530447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10881681996140001797658101 1020157687138125168530447)
    ·
      refine ⟨1530236530707187752795671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1020157687138125168530447 1530236530707187752795671)
      ·
        refine ⟨2295354796060781629193507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1530236530707187752795671 2295354796060781629193507)
        ·
          refine ⟨3443032194091172443790261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2295354796060781629193507 3443032194091172443790261)
          ·
            refine ⟨322784268196047416605337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3443032194091172443790261 322784268196047416605337)
            ·
              refine ⟨242088201147035562454003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 322784268196047416605337 242088201147035562454003)
              ·
                refine ⟨363132301720553343681005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242088201147035562454003 363132301720553343681005)
                ·
                  refine ⟨136174613145207503880377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 363132301720553343681005 136174613145207503880377)
                  ·
                    rfl

theorem cell20_298349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_298349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298349 prefixEnd_298349 := by exact prefixLift 298349
  have htrace : WordTrace (prefixWord ++ tailWord_298349) baseStart_298349 baseEnd_298349 := by
    simpa [prefixWord, tailWord_298349, baseEnd_298349] using wordTrace_append hprefix tailTrace_298349
  have hstable : (prefixWord ++ tailWord_298349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298349).length < 2 ^ (prefixWord ++ tailWord_298349).sum := by decide
  have hdescent : baseEnd_298349 < baseStart_298349 := by decide
  rcases family_descends (prefixWord ++ tailWord_298349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298453 : List Nat := [1, 3, 2, 3, 1, 1, 1, 6, 2]
def baseStart_298453 : Nat := 118140960795 + 298453 * 2 ^ 59
def prefixEnd_298453 : Nat := 4983230072969 + 3 ^ 40 * 298453 * 2
def baseEnd_298453 : Nat := 136222081579045364413285

theorem tailTrace_298453 : CollatzResearch.WordTrace tailWord_298453 prefixEnd_298453 136222081579045364413285 := by
  unfold tailWord_298453
  simp only [CollatzResearch.WordTrace]
  refine ⟨10885475187763227559444013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7256983458508818372962675 10885475187763227559444013)
  ·
    refine ⟨4082053195411210334791505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10885475187763227559444013 4082053195411210334791505)
    ·
      refine ⟨3061539896558407751093629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4082053195411210334791505 3061539896558407751093629)
      ·
        refine ⟨1148077461209402906660111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3061539896558407751093629 1148077461209402906660111)
        ·
          refine ⟨1722116191814104359990167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1148077461209402906660111 1722116191814104359990167)
          ·
            refine ⟨2583174287721156539985251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1722116191814104359990167 2583174287721156539985251)
            ·
              refine ⟨3874761431581734809977877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2583174287721156539985251 3874761431581734809977877)
              ·
                refine ⟨181629442105393819217713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3874761431581734809977877 181629442105393819217713)
                ·
                  refine ⟨136222081579045364413285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 181629442105393819217713 136222081579045364413285)
                  ·
                    rfl

theorem cell20_298453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 6, 2].length) (baseStart_298453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298453 prefixEnd_298453 := by exact prefixLift 298453
  have htrace : WordTrace (prefixWord ++ tailWord_298453) baseStart_298453 baseEnd_298453 := by
    simpa [prefixWord, tailWord_298453, baseEnd_298453] using wordTrace_append hprefix tailTrace_298453
  have hstable : (prefixWord ++ tailWord_298453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298453).length < 2 ^ (prefixWord ++ tailWord_298453).sum := by decide
  have hdescent : baseEnd_298453 < baseStart_298453 := by decide
  rcases family_descends (prefixWord ++ tailWord_298453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298481 : List Nat := [1, 2, 2, 2, 3, 3, 1, 6]
def baseStart_298481 : Nat := 118140960795 + 298481 * 2 ^ 59
def prefixEnd_298481 : Nat := 4983230072969 + 3 ^ 40 * 298481 * 2
def baseEnd_298481 : Nat := 45411620514000570493279

theorem tailTrace_298481 : CollatzResearch.WordTrace tailWord_298481 prefixEnd_298481 45411620514000570493279 := by
  unfold tailWord_298481
  simp only [CollatzResearch.WordTrace]
  refine ⟨10886496431661788341463297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7257664287774525560975531 10886496431661788341463297)
  ·
    refine ⟨8164872323746341256097473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10886496431661788341463297 8164872323746341256097473)
    ·
      refine ⟨6123654242809755942073105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8164872323746341256097473 6123654242809755942073105)
      ·
        refine ⟨4592740682107316956554829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6123654242809755942073105 4592740682107316956554829)
        ·
          refine ⟨1722277755790243858708061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4592740682107316956554829 1722277755790243858708061)
          ·
            refine ⟨645854158421341447015523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1722277755790243858708061 645854158421341447015523)
            ·
              refine ⟨968781237632012170523285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 645854158421341447015523 968781237632012170523285)
              ·
                refine ⟨45411620514000570493279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 968781237632012170523285 45411620514000570493279)
                ·
                  rfl

theorem cell20_298481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 6].length) (baseStart_298481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298481 prefixEnd_298481 := by exact prefixLift 298481
  have htrace : WordTrace (prefixWord ++ tailWord_298481) baseStart_298481 baseEnd_298481 := by
    simpa [prefixWord, tailWord_298481, baseEnd_298481] using wordTrace_append hprefix tailTrace_298481
  have hstable : (prefixWord ++ tailWord_298481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298481).length < 2 ^ (prefixWord ++ tailWord_298481).sum := by decide
  have hdescent : baseEnd_298481 < baseStart_298481 := by decide
  rcases family_descends (prefixWord ++ tailWord_298481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298488 : List Nat := [2, 1, 2, 1, 1, 5, 1, 2, 5]
def baseStart_298488 : Nat := 118140960795 + 298488 * 2 ^ 59
def prefixEnd_298488 : Nat := 4983230072969 + 3 ^ 40 * 298488 * 2
def baseEnd_298488 : Nat := 136238056532740798246475

theorem tailTrace_298488 : CollatzResearch.WordTrace tailWord_298488 prefixEnd_298488 136238056532740798246475 := by
  unfold tailWord_298488
  simp only [CollatzResearch.WordTrace]
  refine ⟨5443375871318214268484059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7257834495090952357978745 5443375871318214268484059)
  ·
    refine ⟨8165063806977321402726089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5443375871318214268484059 8165063806977321402726089)
    ·
      refine ⟨6123797855232991052044567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8165063806977321402726089 6123797855232991052044567)
      ·
        refine ⟨9185696782849486578066851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6123797855232991052044567 9185696782849486578066851)
        ·
          refine ⟨13778545174274229867100277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9185696782849486578066851 13778545174274229867100277)
          ·
            refine ⟨1291738610088209050040651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13778545174274229867100277 1291738610088209050040651)
            ·
              refine ⟨1937607915132313575060977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1291738610088209050040651 1937607915132313575060977)
              ·
                refine ⟨1453205936349235181295733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1937607915132313575060977 1453205936349235181295733)
                ·
                  refine ⟨136238056532740798246475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1453205936349235181295733 136238056532740798246475)
                  ·
                    rfl

theorem cell20_298488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_298488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298488 prefixEnd_298488 := by exact prefixLift 298488
  have htrace : WordTrace (prefixWord ++ tailWord_298488) baseStart_298488 baseEnd_298488 := by
    simpa [prefixWord, tailWord_298488, baseEnd_298488] using wordTrace_append hprefix tailTrace_298488
  have hstable : (prefixWord ++ tailWord_298488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298488).length < 2 ^ (prefixWord ++ tailWord_298488).sum := by decide
  have hdescent : baseEnd_298488 < baseStart_298488 := by decide
  rcases family_descends (prefixWord ++ tailWord_298488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298494 : List Nat := [4, 2, 2, 3, 2, 1, 6]
def baseStart_298494 : Nat := 118140960795 + 298494 * 2 ^ 59
def prefixEnd_298494 : Nat := 4983230072969 + 3 ^ 40 * 298494 * 2
def baseEnd_298494 : Nat := 15137866121803493782939

theorem tailTrace_298494 : CollatzResearch.WordTrace tailWord_298494 prefixEnd_298494 15137866121803493782939 := by
  unfold tailWord_298494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1360871322576836445210817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7257980387076461041124357 1360871322576836445210817)
  ·
    refine ⟨1020653491932627333908113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1360871322576836445210817 1020653491932627333908113)
    ·
      refine ⟨765490118949470500431085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1020653491932627333908113 765490118949470500431085)
      ·
        refine ⟨287058794606051437661657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 765490118949470500431085 287058794606051437661657)
        ·
          refine ⟨215294095954538578246243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287058794606051437661657 215294095954538578246243)
          ·
            refine ⟨322941143931807867369365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215294095954538578246243 322941143931807867369365)
            ·
              refine ⟨15137866121803493782939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 322941143931807867369365 15137866121803493782939)
              ·
                rfl

theorem cell20_298494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 6].length) (baseStart_298494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298494 prefixEnd_298494 := by exact prefixLift 298494
  have htrace : WordTrace (prefixWord ++ tailWord_298494) baseStart_298494 baseEnd_298494 := by
    simpa [prefixWord, tailWord_298494, baseEnd_298494] using wordTrace_append hprefix tailTrace_298494
  have hstable : (prefixWord ++ tailWord_298494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298494).length < 2 ^ (prefixWord ++ tailWord_298494).sum := by decide
  have hdescent : baseEnd_298494 < baseStart_298494 := by decide
  rcases family_descends (prefixWord ++ tailWord_298494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298498 : List Nat := [3, 4, 1, 2, 1, 1, 8]
def baseStart_298498 : Nat := 118140960795 + 298498 * 2 ^ 59
def prefixEnd_298498 : Nat := 4983230072969 + 3 ^ 40 * 298498 * 2
def baseEnd_298498 : Nat := 15138068978358356434789

theorem tailTrace_298498 : CollatzResearch.WordTrace tailWord_298498 prefixEnd_298498 15138068978358356434789 := by
  unfold tailWord_298498
  simp only [CollatzResearch.WordTrace]
  refine ⟨2721779118150050061208037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7258077648400133496554765 2721779118150050061208037)
  ·
    refine ⟨510333584653134386476507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2721779118150050061208037 510333584653134386476507)
    ·
      refine ⟨765500376979701579714761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 510333584653134386476507 765500376979701579714761)
      ·
        refine ⟨574125282734776184786071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 765500376979701579714761 574125282734776184786071)
        ·
          refine ⟨861187924102164277179107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 574125282734776184786071 861187924102164277179107)
          ·
            refine ⟨1291781886153246415768661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 861187924102164277179107 1291781886153246415768661)
            ·
              refine ⟨15138068978358356434789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1291781886153246415768661 15138068978358356434789)
              ·
                rfl

theorem cell20_298498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 8].length) (baseStart_298498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298498 prefixEnd_298498 := by exact prefixLift 298498
  have htrace : WordTrace (prefixWord ++ tailWord_298498) baseStart_298498 baseEnd_298498 := by
    simpa [prefixWord, tailWord_298498, baseEnd_298498] using wordTrace_append hprefix tailTrace_298498
  have hstable : (prefixWord ++ tailWord_298498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298498).length < 2 ^ (prefixWord ++ tailWord_298498).sum := by decide
  have hdescent : baseEnd_298498 < baseStart_298498 := by decide
  rcases family_descends (prefixWord ++ tailWord_298498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298508 : List Nat := [2, 2, 1, 2, 6, 1, 1, 1, 4]
def baseStart_298508 : Nat := 118140960795 + 298508 * 2 ^ 59
def prefixEnd_298508 : Nat := 4983230072969 + 3 ^ 40 * 298508 * 2
def baseEnd_298508 : Nat := 136247185077709617579727

theorem tailTrace_298508 : CollatzResearch.WordTrace tailWord_298508 prefixEnd_298508 136247185077709617579727 := by
  unfold tailWord_298508
  simp only [CollatzResearch.WordTrace]
  refine ⟨5443740601281985976348089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7258320801709314635130785 5443740601281985976348089)
  ·
    refine ⟨4082805450961489482261067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5443740601281985976348089 4082805450961489482261067)
    ·
      refine ⟨6124208176442234223391601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4082805450961489482261067 6124208176442234223391601)
      ·
        refine ⟨4593156132331675667543701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6124208176442234223391601 4593156132331675667543701)
        ·
          refine ⟨215304193703047296916111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4593156132331675667543701 215304193703047296916111)
          ·
            refine ⟨322956290554570945374167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215304193703047296916111 322956290554570945374167)
            ·
              refine ⟨484434435831856418061251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322956290554570945374167 484434435831856418061251)
              ·
                refine ⟨726651653747784627091877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 484434435831856418061251 726651653747784627091877)
                ·
                  refine ⟨136247185077709617579727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 726651653747784627091877 136247185077709617579727)
                  ·
                    rfl

theorem cell20_298508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 4].length) (baseStart_298508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298508 prefixEnd_298508 := by exact prefixLift 298508
  have htrace : WordTrace (prefixWord ++ tailWord_298508) baseStart_298508 baseEnd_298508 := by
    simpa [prefixWord, tailWord_298508, baseEnd_298508] using wordTrace_append hprefix tailTrace_298508
  have hstable : (prefixWord ++ tailWord_298508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298508).length < 2 ^ (prefixWord ++ tailWord_298508).sum := by decide
  have hdescent : baseEnd_298508 < baseStart_298508 := by decide
  rcases family_descends (prefixWord ++ tailWord_298508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298533 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 6]
def baseStart_298533 : Nat := 118140960795 + 298533 * 2 ^ 59
def prefixEnd_298533 : Nat := 4983230072969 + 3 ^ 40 * 298533 * 2
def baseEnd_298533 : Nat := 136258595758920641746291

theorem tailTrace_298533 : CollatzResearch.WordTrace tailWord_298533 prefixEnd_298533 136258595758920641746291 := by
  unfold tailWord_298533
  simp only [CollatzResearch.WordTrace]
  refine ⟨10888393027473401222356253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7258928684982267481570835 10888393027473401222356253)
  ·
    refine ⟨4083147385302525458383595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10888393027473401222356253 4083147385302525458383595)
    ·
      refine ⟨6124721077953788187575393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4083147385302525458383595 6124721077953788187575393)
      ·
        refine ⟨4593540808465341140681545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6124721077953788187575393 4593540808465341140681545)
        ·
          refine ⟨3445155606349005855511159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4593540808465341140681545 3445155606349005855511159)
          ·
            refine ⟨5167733409523508783266739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3445155606349005855511159 5167733409523508783266739)
            ·
              refine ⟨7751600114285263174900109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5167733409523508783266739 7751600114285263174900109)
              ·
                refine ⟨2906850042856973690587541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7751600114285263174900109 2906850042856973690587541)
                ·
                  refine ⟨136258595758920641746291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2906850042856973690587541 136258595758920641746291)
                  ·
                    rfl

theorem cell20_298533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_298533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298533 prefixEnd_298533 := by exact prefixLift 298533
  have htrace : WordTrace (prefixWord ++ tailWord_298533) baseStart_298533 baseEnd_298533 := by
    simpa [prefixWord, tailWord_298533, baseEnd_298533] using wordTrace_append hprefix tailTrace_298533
  have hstable : (prefixWord ++ tailWord_298533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298533).length < 2 ^ (prefixWord ++ tailWord_298533).sum := by decide
  have hdescent : baseEnd_298533 < baseStart_298533 := by decide
  rcases family_descends (prefixWord ++ tailWord_298533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298557 : List Nat := [1, 4, 1, 3, 3, 8]
def baseStart_298557 : Nat := 118140960795 + 298557 * 2 ^ 59
def prefixEnd_298557 : Nat := 4983230072969 + 3 ^ 40 * 298557 * 2
def baseEnd_298557 : Nat := 5047020370847526849859

theorem tailTrace_298557 : CollatzResearch.WordTrace tailWord_298557 prefixEnd_298557 5047020370847526849859 := by
  unfold tailWord_298557
  simp only [CollatzResearch.WordTrace]
  refine ⟨10889268379386453321229925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7259512252924302214153283 10889268379386453321229925)
  ·
    refine ⟨2041737821134959997730611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10889268379386453321229925 2041737821134959997730611)
    ·
      refine ⟨3062606731702439996595917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2041737821134959997730611 3062606731702439996595917)
      ·
        refine ⟨1148477524388414998723469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3062606731702439996595917 1148477524388414998723469)
        ·
          refine ⟨430679071645655624521301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1148477524388414998723469 430679071645655624521301)
          ·
            refine ⟨5047020370847526849859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 430679071645655624521301 5047020370847526849859)
            ·
              rfl

theorem cell20_298557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 8].length) (baseStart_298557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298557 prefixEnd_298557 := by exact prefixLift 298557
  have htrace : WordTrace (prefixWord ++ tailWord_298557) baseStart_298557 baseEnd_298557 := by
    simpa [prefixWord, tailWord_298557, baseEnd_298557] using wordTrace_append hprefix tailTrace_298557
  have hstable : (prefixWord ++ tailWord_298557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298557).length < 2 ^ (prefixWord ++ tailWord_298557).sum := by decide
  have hdescent : baseEnd_298557 < baseStart_298557 := by decide
  rcases family_descends (prefixWord ++ tailWord_298557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298571 : List Nat := [1, 1, 1, 1, 3, 1, 3, 5, 4]
def baseStart_298571 : Nat := 118140960795 + 298571 * 2 ^ 59
def prefixEnd_298571 : Nat := 4983230072969 + 3 ^ 40 * 298571 * 2
def baseEnd_298571 : Nat := 136275939994361398479469

theorem tailTrace_298571 : CollatzResearch.WordTrace tailWord_298571 prefixEnd_298571 136275939994361398479469 := by
  unfold tailWord_298571
  simp only [CollatzResearch.WordTrace]
  refine ⟨10889779001335733712239567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7259852667557155808159711 10889779001335733712239567)
  ·
    refine ⟨16334668502003600568359351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10889779001335733712239567 16334668502003600568359351)
    ·
      refine ⟨24502002753005400852539027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16334668502003600568359351 24502002753005400852539027)
      ·
        refine ⟨36753004129508101278808541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24502002753005400852539027 36753004129508101278808541)
        ·
          refine ⟨13782376548565537979553203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36753004129508101278808541 13782376548565537979553203)
          ·
            refine ⟨20673564822848306969329805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13782376548565537979553203 20673564822848306969329805)
            ·
              refine ⟨7752586808568115113498677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20673564822848306969329805 7752586808568115113498677)
              ·
                refine ⟨726805013303260791890501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7752586808568115113498677 726805013303260791890501)
                ·
                  refine ⟨136275939994361398479469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 726805013303260791890501 136275939994361398479469)
                  ·
                    rfl

theorem cell20_298571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 4].length) (baseStart_298571 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298571 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298571 prefixEnd_298571 := by exact prefixLift 298571
  have htrace : WordTrace (prefixWord ++ tailWord_298571) baseStart_298571 baseEnd_298571 := by
    simpa [prefixWord, tailWord_298571, baseEnd_298571] using wordTrace_append hprefix tailTrace_298571
  have hstable : (prefixWord ++ tailWord_298571).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298571).length < 2 ^ (prefixWord ++ tailWord_298571).sum := by decide
  have hdescent : baseEnd_298571 < baseStart_298571 := by decide
  rcases family_descends (prefixWord ++ tailWord_298571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298588 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 6]
def baseStart_298588 : Nat := 118140960795 + 298588 * 2 ^ 59
def prefixEnd_298588 : Nat := 4983230072969 + 3 ^ 40 * 298588 * 2
def baseEnd_298588 : Nat := 136283699257584894912733

theorem tailTrace_298588 : CollatzResearch.WordTrace tailWord_298588 prefixEnd_298588 136283699257584894912733 := by
  unfold tailWord_298588
  simp only [CollatzResearch.WordTrace]
  refine ⟨5445199521137072807804209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7260266028182763743738945 5445199521137072807804209)
  ·
    refine ⟨4083899640852804605853157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5445199521137072807804209 4083899640852804605853157)
    ·
      refine ⟨765731182659900863597467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4083899640852804605853157 765731182659900863597467)
      ·
        refine ⟨1148596773989851295396201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 765731182659900863597467 1148596773989851295396201)
        ·
          refine ⟨861447580492388471547151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1148596773989851295396201 861447580492388471547151)
          ·
            refine ⟨1292171370738582707320727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 861447580492388471547151 1292171370738582707320727)
            ·
              refine ⟨1938257056107874060981091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1292171370738582707320727 1938257056107874060981091)
              ·
                refine ⟨2907385584161811091471637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1938257056107874060981091 2907385584161811091471637)
                ·
                  refine ⟨136283699257584894912733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2907385584161811091471637 136283699257584894912733)
                  ·
                    rfl

theorem cell20_298588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_298588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298588 prefixEnd_298588 := by exact prefixLift 298588
  have htrace : WordTrace (prefixWord ++ tailWord_298588) baseStart_298588 baseEnd_298588 := by
    simpa [prefixWord, tailWord_298588, baseEnd_298588] using wordTrace_append hprefix tailTrace_298588
  have hstable : (prefixWord ++ tailWord_298588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298588).length < 2 ^ (prefixWord ++ tailWord_298588).sum := by decide
  have hdescent : baseEnd_298588 < baseStart_298588 := by decide
  rcases family_descends (prefixWord ++ tailWord_298588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298640 : List Nat := [2, 1, 1, 1, 1, 1, 3, 7, 3]
def baseStart_298640 : Nat := 118140960795 + 298640 * 2 ^ 59
def prefixEnd_298640 : Nat := 4983230072969 + 3 ^ 40 * 298640 * 2
def baseEnd_298640 : Nat := 136307433474503825179187

theorem tailTrace_298640 : CollatzResearch.WordTrace tailWord_298640 prefixEnd_298640 136307433474503825179187 := by
  unfold tailWord_298640
  simp only [CollatzResearch.WordTrace]
  refine ⟨5446147819042879248250687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7261530425390505664334249 5446147819042879248250687)
  ·
    refine ⟨8169221728564318872376031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5446147819042879248250687 8169221728564318872376031)
    ·
      refine ⟨12253832592846478308564047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8169221728564318872376031 12253832592846478308564047)
      ·
        refine ⟨18380748889269717462846071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12253832592846478308564047 18380748889269717462846071)
        ·
          refine ⟨27571123333904576194269107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18380748889269717462846071 27571123333904576194269107)
          ·
            refine ⟨41356685000856864291403661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27571123333904576194269107 41356685000856864291403661)
            ·
              refine ⟨15508756875321324109276373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41356685000856864291403661 15508756875321324109276373)
              ·
                refine ⟨363486489265343533811165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15508756875321324109276373 363486489265343533811165)
                ·
                  refine ⟨136307433474503825179187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 363486489265343533811165 136307433474503825179187)
                  ·
                    rfl

theorem cell20_298640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 3].length) (baseStart_298640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298640 prefixEnd_298640 := by exact prefixLift 298640
  have htrace : WordTrace (prefixWord ++ tailWord_298640) baseStart_298640 baseEnd_298640 := by
    simpa [prefixWord, tailWord_298640, baseEnd_298640] using wordTrace_append hprefix tailTrace_298640
  have hstable : (prefixWord ++ tailWord_298640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298640).length < 2 ^ (prefixWord ++ tailWord_298640).sum := by decide
  have hdescent : baseEnd_298640 < baseStart_298640 := by decide
  rcases family_descends (prefixWord ++ tailWord_298640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298660 : List Nat := [2, 3, 1, 2, 2, 4, 1, 3, 2]
def baseStart_298660 : Nat := 118140960795 + 298660 * 2 ^ 59
def prefixEnd_298660 : Nat := 4983230072969 + 3 ^ 40 * 298660 * 2
def baseEnd_298660 : Nat := 136316562019472644512439

theorem tailTrace_298660 : CollatzResearch.WordTrace tailWord_298660 prefixEnd_298660 136316562019472644512439 := by
  unfold tailWord_298660
  simp only [CollatzResearch.WordTrace]
  refine ⟨5446512549006650956114717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7262016732008867941486289 5446512549006650956114717)
  ·
    refine ⟨2042442205877494108543019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5446512549006650956114717 2042442205877494108543019)
    ·
      refine ⟨3063663308816241162814529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2042442205877494108543019 3063663308816241162814529)
      ·
        refine ⟨2297747481612180872110897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3063663308816241162814529 2297747481612180872110897)
        ·
          refine ⟨1723310611209135654083173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2297747481612180872110897 1723310611209135654083173)
          ·
            refine ⟨323120739601712935140595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1723310611209135654083173 323120739601712935140595)
            ·
              refine ⟨484681109402569402710893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323120739601712935140595 484681109402569402710893)
              ·
                refine ⟨181755416025963526016585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 484681109402569402710893 181755416025963526016585)
                ·
                  refine ⟨136316562019472644512439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 181755416025963526016585 136316562019472644512439)
                  ·
                    rfl

theorem cell20_298660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_298660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298660 prefixEnd_298660 := by exact prefixLift 298660
  have htrace : WordTrace (prefixWord ++ tailWord_298660) baseStart_298660 baseEnd_298660 := by
    simpa [prefixWord, tailWord_298660, baseEnd_298660] using wordTrace_append hprefix tailTrace_298660
  have hstable : (prefixWord ++ tailWord_298660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298660).length < 2 ^ (prefixWord ++ tailWord_298660).sum := by decide
  have hdescent : baseEnd_298660 < baseStart_298660 := by decide
  rcases family_descends (prefixWord ++ tailWord_298660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298677 : List Nat := [1, 3, 3, 3, 2, 1, 3, 2, 2]
def baseStart_298677 : Nat := 118140960795 + 298677 * 2 ^ 59
def prefixEnd_298677 : Nat := 4983230072969 + 3 ^ 40 * 298677 * 2
def baseEnd_298677 : Nat := 136324321282696140945703

theorem tailTrace_298677 : CollatzResearch.WordTrace tailWord_298677 prefixEnd_298677 136324321282696140945703 := by
  unfold tailWord_298677
  simp only [CollatzResearch.WordTrace]
  refine ⟨10893645138951713815598285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7262430092634475877065523 10893645138951713815598285)
  ·
    refine ⟨4085116927106892680849357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10893645138951713815598285 4085116927106892680849357)
    ·
      refine ⟨1531918847665084755318509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4085116927106892680849357 1531918847665084755318509)
      ·
        refine ⟨574469567874406783244441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1531918847665084755318509 574469567874406783244441)
        ·
          refine ⟨430852175905805087433331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 574469567874406783244441 430852175905805087433331)
          ·
            refine ⟨646278263858707631149997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 430852175905805087433331 646278263858707631149997)
            ·
              refine ⟨242354348947015361681249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 646278263858707631149997 242354348947015361681249)
              ·
                refine ⟨181765761710261521260937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242354348947015361681249 181765761710261521260937)
                ·
                  refine ⟨136324321282696140945703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 181765761710261521260937 136324321282696140945703)
                  ·
                    rfl

theorem cell20_298677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 2, 2].length) (baseStart_298677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298677 prefixEnd_298677 := by exact prefixLift 298677
  have htrace : WordTrace (prefixWord ++ tailWord_298677) baseStart_298677 baseEnd_298677 := by
    simpa [prefixWord, tailWord_298677, baseEnd_298677] using wordTrace_append hprefix tailTrace_298677
  have hstable : (prefixWord ++ tailWord_298677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298677).length < 2 ^ (prefixWord ++ tailWord_298677).sum := by decide
  have hdescent : baseEnd_298677 < baseStart_298677 := by decide
  rcases family_descends (prefixWord ++ tailWord_298677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298733 : List Nat := [1, 5, 1, 2, 1, 2, 1, 4, 3]
def baseStart_298733 : Nat := 118140960795 + 298733 * 2 ^ 59
def prefixEnd_298733 : Nat := 4983230072969 + 3 ^ 40 * 298733 * 2
def baseEnd_298733 : Nat := 136349881208608835078807

theorem tailTrace_298733 : CollatzResearch.WordTrace tailWord_298733 prefixEnd_298733 136349881208608835078807 := by
  unfold tailWord_298733
  simp only [CollatzResearch.WordTrace]
  refine ⟨10895687626748835379636853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7263791751165890253091235 10895687626748835379636853)
  ·
    refine ⟨1021470715007703316840955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10895687626748835379636853 1021470715007703316840955)
    ·
      refine ⟨1532206072511554975261433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1021470715007703316840955 1532206072511554975261433)
      ·
        refine ⟨1149154554383666231446075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1532206072511554975261433 1149154554383666231446075)
        ·
          refine ⟨1723731831575499347169113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1149154554383666231446075 1723731831575499347169113)
          ·
            refine ⟨1292798873681624510376835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1723731831575499347169113 1292798873681624510376835)
            ·
              refine ⟨1939198310522436765565253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1292798873681624510376835 1939198310522436765565253)
              ·
                refine ⟨363599683222956893543485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1939198310522436765565253 363599683222956893543485)
                ·
                  refine ⟨136349881208608835078807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 363599683222956893543485 136349881208608835078807)
                  ·
                    rfl

theorem cell20_298733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_298733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298733 prefixEnd_298733 := by exact prefixLift 298733
  have htrace : WordTrace (prefixWord ++ tailWord_298733) baseStart_298733 baseEnd_298733 := by
    simpa [prefixWord, tailWord_298733, baseEnd_298733] using wordTrace_append hprefix tailTrace_298733
  have hstable : (prefixWord ++ tailWord_298733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298733).length < 2 ^ (prefixWord ++ tailWord_298733).sum := by decide
  have hdescent : baseEnd_298733 < baseStart_298733 := by decide
  rcases family_descends (prefixWord ++ tailWord_298733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298788 : List Nat := [2, 3, 1, 3, 2, 3, 1, 2, 3]
def baseStart_298788 : Nat := 118140960795 + 298788 * 2 ^ 59
def prefixEnd_298788 : Nat := 4983230072969 + 3 ^ 40 * 298788 * 2
def baseEnd_298788 : Nat := 136374984707273088245249

theorem tailTrace_298788 : CollatzResearch.WordTrace tailWord_298788 prefixEnd_298788 136374984707273088245249 := by
  unfold tailWord_298788
  simp only [CollatzResearch.WordTrace]
  refine ⟨5448846820774789886444509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7265129094366386515259345 5448846820774789886444509)
  ·
    refine ⟨2043317557790546207416691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5448846820774789886444509 2043317557790546207416691)
    ·
      refine ⟨3064976336685819311125037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2043317557790546207416691 3064976336685819311125037)
      ·
        refine ⟨1149366126257182241671889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3064976336685819311125037 1149366126257182241671889)
        ·
          refine ⟨862024594692886681253917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1149366126257182241671889 862024594692886681253917)
          ·
            refine ⟨323259223009832505470219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 862024594692886681253917 323259223009832505470219)
            ·
              refine ⟨484888834514748758205329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323259223009832505470219 484888834514748758205329)
              ·
                refine ⟨363666625886061568653997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 484888834514748758205329 363666625886061568653997)
                ·
                  refine ⟨136374984707273088245249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 363666625886061568653997 136374984707273088245249)
                  ·
                    rfl

theorem cell20_298788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_298788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298788 prefixEnd_298788 := by exact prefixLift 298788
  have htrace : WordTrace (prefixWord ++ tailWord_298788) baseStart_298788 baseEnd_298788 := by
    simpa [prefixWord, tailWord_298788, baseEnd_298788] using wordTrace_append hprefix tailTrace_298788
  have hstable : (prefixWord ++ tailWord_298788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298788).length < 2 ^ (prefixWord ++ tailWord_298788).sum := by decide
  have hdescent : baseEnd_298788 < baseStart_298788 := by decide
  rcases family_descends (prefixWord ++ tailWord_298788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298823 : List Nat := [1, 1, 4, 1, 2, 1, 6, 4]
def baseStart_298823 : Nat := 118140960795 + 298823 * 2 ^ 59
def prefixEnd_298823 : Nat := 4983230072969 + 3 ^ 40 * 298823 * 2
def baseEnd_298823 : Nat := 45463653220322840692813

theorem tailTrace_298823 : CollatzResearch.WordTrace tailWord_298823 prefixEnd_298823 45463653220322840692813 := by
  unfold tailWord_298823
  simp only [CollatzResearch.WordTrace]
  refine ⟨10898970196422780750413123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7265980130948520500275415 10898970196422780750413123)
  ·
    refine ⟨16348455294634171125619685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10898970196422780750413123 16348455294634171125619685)
    ·
      refine ⟨3065335367743907086053691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16348455294634171125619685 3065335367743907086053691)
      ·
        refine ⟨4598003051615860629080537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3065335367743907086053691 4598003051615860629080537)
        ·
          refine ⟨3448502288711895471810403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4598003051615860629080537 3448502288711895471810403)
          ·
            refine ⟨5172753433067843207715605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3448502288711895471810403 5172753433067843207715605)
            ·
              refine ⟨242472817175055150361669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5172753433067843207715605 242472817175055150361669)
              ·
                refine ⟨45463653220322840692813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 242472817175055150361669 45463653220322840692813)
                ·
                  rfl

theorem cell20_298823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 4].length) (baseStart_298823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298823 prefixEnd_298823 := by exact prefixLift 298823
  have htrace : WordTrace (prefixWord ++ tailWord_298823) baseStart_298823 baseEnd_298823 := by
    simpa [prefixWord, tailWord_298823, baseEnd_298823] using wordTrace_append hprefix tailTrace_298823
  have hstable : (prefixWord ++ tailWord_298823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298823).length < 2 ^ (prefixWord ++ tailWord_298823).sum := by decide
  have hdescent : baseEnd_298823 < baseStart_298823 := by decide
  rcases family_descends (prefixWord ++ tailWord_298823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298829 : List Nat := [1, 6, 1, 2, 1, 3, 1, 3, 2]
def baseStart_298829 : Nat := 118140960795 + 298829 * 2 ^ 59
def prefixEnd_298829 : Nat := 4983230072969 + 3 ^ 40 * 298829 * 2
def baseEnd_298829 : Nat := 136393698224459167878415

theorem tailTrace_298829 : CollatzResearch.WordTrace tailWord_298829 prefixEnd_298829 136393698224459167878415 := by
  unfold tailWord_298829
  simp only [CollatzResearch.WordTrace]
  refine ⟨10899189034401043775131541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7266126022934029183421027 10899189034401043775131541)
  ·
    refine ⟨510899485987548926959291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10899189034401043775131541 510899485987548926959291)
    ·
      refine ⟨766349228981323390438937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 510899485987548926959291 766349228981323390438937)
      ·
        refine ⟨574761921735992542829203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 766349228981323390438937 574761921735992542829203)
        ·
          refine ⟨862142882603988814243805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 574761921735992542829203 862142882603988814243805)
          ·
            refine ⟨323303580976495805341427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 862142882603988814243805 323303580976495805341427)
            ·
              refine ⟨484955371464743708012141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323303580976495805341427 484955371464743708012141)
              ·
                refine ⟨181858264299278890504553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 484955371464743708012141 181858264299278890504553)
                ·
                  refine ⟨136393698224459167878415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 181858264299278890504553 136393698224459167878415)
                  ·
                    rfl

theorem cell20_298829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_298829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298829 prefixEnd_298829 := by exact prefixLift 298829
  have htrace : WordTrace (prefixWord ++ tailWord_298829) baseStart_298829 baseEnd_298829 := by
    simpa [prefixWord, tailWord_298829, baseEnd_298829] using wordTrace_append hprefix tailTrace_298829
  have hstable : (prefixWord ++ tailWord_298829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298829).length < 2 ^ (prefixWord ++ tailWord_298829).sum := by decide
  have hdescent : baseEnd_298829 < baseStart_298829 := by decide
  rcases family_descends (prefixWord ++ tailWord_298829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298833 : List Nat := [1, 2, 2, 1, 5, 1, 3, 3, 2]
def baseStart_298833 : Nat := 118140960795 + 298833 * 2 ^ 59
def prefixEnd_298833 : Nat := 4983230072969 + 3 ^ 40 * 298833 * 2
def baseEnd_298833 : Nat := 136395523933452931745065

theorem tailTrace_298833 : CollatzResearch.WordTrace tailWord_298833 prefixEnd_298833 136395523933452931745065 := by
  unfold tailWord_298833
  simp only [CollatzResearch.WordTrace]
  refine ⟨10899334926386552458277153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7266223284257701638851435 10899334926386552458277153)
  ·
    refine ⟨8174501194789914343707865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10899334926386552458277153 8174501194789914343707865)
    ·
      refine ⟨6130875896092435757780899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8174501194789914343707865 6130875896092435757780899)
      ·
        refine ⟨9196313844138653636671349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6130875896092435757780899 9196313844138653636671349)
        ·
          refine ⟨862154422887998778437939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9196313844138653636671349 862154422887998778437939)
          ·
            refine ⟨1293231634331998167656909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 862154422887998778437939 1293231634331998167656909)
            ·
              refine ⟨484961862874499312871341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1293231634331998167656909 484961862874499312871341)
              ·
                refine ⟨181860698577937242326753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 484961862874499312871341 181860698577937242326753)
                ·
                  refine ⟨136395523933452931745065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 181860698577937242326753 136395523933452931745065)
                  ·
                    rfl

theorem cell20_298833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 3, 2].length) (baseStart_298833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298833 prefixEnd_298833 := by exact prefixLift 298833
  have htrace : WordTrace (prefixWord ++ tailWord_298833) baseStart_298833 baseEnd_298833 := by
    simpa [prefixWord, tailWord_298833, baseEnd_298833] using wordTrace_append hprefix tailTrace_298833
  have hstable : (prefixWord ++ tailWord_298833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298833).length < 2 ^ (prefixWord ++ tailWord_298833).sum := by decide
  have hdescent : baseEnd_298833 < baseStart_298833 := by decide
  rcases family_descends (prefixWord ++ tailWord_298833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298878 : List Nat := [4, 2, 3, 1, 1, 1, 2, 6]
def baseStart_298878 : Nat := 118140960795 + 298878 * 2 ^ 59
def prefixEnd_298878 : Nat := 4983230072969 + 3 ^ 40 * 298878 * 2
def baseEnd_298878 : Nat := 45472021053210925081627

theorem tailTrace_298878 : CollatzResearch.WordTrace tailWord_298878 prefixEnd_298878 45472021053210925081627 := by
  unfold tailWord_298878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1362622026402940642958161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7267317474149016762443525 1362622026402940642958161)
  ·
    refine ⟨1021966519802205482218621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1362622026402940642958161 1021966519802205482218621)
    ·
      refine ⟨383237444925827055831983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1021966519802205482218621 383237444925827055831983)
      ·
        refine ⟨574856167388740583747975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383237444925827055831983 574856167388740583747975)
        ·
          refine ⟨862284251083110875621963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 574856167388740583747975 862284251083110875621963)
          ·
            refine ⟨1293426376624666313432945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 862284251083110875621963 1293426376624666313432945)
            ·
              refine ⟨970069782468499735074709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1293426376624666313432945 970069782468499735074709)
              ·
                refine ⟨45472021053210925081627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 970069782468499735074709 45472021053210925081627)
                ·
                  rfl

theorem cell20_298878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_298878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298878 prefixEnd_298878 := by exact prefixLift 298878
  have htrace : WordTrace (prefixWord ++ tailWord_298878) baseStart_298878 baseEnd_298878 := by
    simpa [prefixWord, tailWord_298878, baseEnd_298878] using wordTrace_append hprefix tailTrace_298878
  have hstable : (prefixWord ++ tailWord_298878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298878).length < 2 ^ (prefixWord ++ tailWord_298878).sum := by decide
  have hdescent : baseEnd_298878 < baseStart_298878 := by decide
  rcases family_descends (prefixWord ++ tailWord_298878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298892 : List Nat := [2, 2, 1, 2, 1, 2, 1, 7, 2]
def baseStart_298892 : Nat := 118140960795 + 298892 * 2 ^ 59
def prefixEnd_298892 : Nat := 4983230072969 + 3 ^ 40 * 298892 * 2
def baseEnd_298892 : Nat := 136422453141110948778157

theorem tailTrace_298892 : CollatzResearch.WordTrace tailWord_298892 prefixEnd_298892 136422453141110948778157 := by
  unfold tailWord_298892
  simp only [CollatzResearch.WordTrace]
  refine ⟨5450743416586402767337465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7267657888781870356449953 5450743416586402767337465)
  ·
    refine ⟨4088057562439802075503099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5450743416586402767337465 4088057562439802075503099)
    ·
      refine ⟨6132086343659703113254649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4088057562439802075503099 6132086343659703113254649)
      ·
        refine ⟨4599064757744777334940987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6132086343659703113254649 4599064757744777334940987)
        ·
          refine ⟨6898597136617166002411481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4599064757744777334940987 6898597136617166002411481)
          ·
            refine ⟨5173947852462874501808611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6898597136617166002411481 5173947852462874501808611)
            ·
              refine ⟨7760921778694311752712917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5173947852462874501808611 7760921778694311752712917)
              ·
                refine ⟨181896604188147931704209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7760921778694311752712917 181896604188147931704209)
                ·
                  refine ⟨136422453141110948778157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 181896604188147931704209 136422453141110948778157)
                  ·
                    rfl

theorem cell20_298892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 7, 2].length) (baseStart_298892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298892 prefixEnd_298892 := by exact prefixLift 298892
  have htrace : WordTrace (prefixWord ++ tailWord_298892) baseStart_298892 baseEnd_298892 := by
    simpa [prefixWord, tailWord_298892, baseEnd_298892] using wordTrace_append hprefix tailTrace_298892
  have hstable : (prefixWord ++ tailWord_298892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298892).length < 2 ^ (prefixWord ++ tailWord_298892).sum := by decide
  have hdescent : baseEnd_298892 < baseStart_298892 := by decide
  rcases family_descends (prefixWord ++ tailWord_298892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298909 : List Nat := [1, 4, 2, 1, 2, 3, 1, 4, 2]
def baseStart_298909 : Nat := 118140960795 + 298909 * 2 ^ 59
def prefixEnd_298909 : Nat := 4983230072969 + 3 ^ 40 * 298909 * 2
def baseEnd_298909 : Nat := 136430212404334445211421

theorem tailTrace_298909 : CollatzResearch.WordTrace tailWord_298909 prefixEnd_298909 136430212404334445211421 := by
  unfold tailWord_298909
  simp only [CollatzResearch.WordTrace]
  refine ⟨10902106874111217438043781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7268071249407478292029187 10902106874111217438043781)
  ·
    refine ⟨2044145038895853269633209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10902106874111217438043781 2044145038895853269633209)
    ·
      refine ⟨1533108779171889952224907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2044145038895853269633209 1533108779171889952224907)
      ·
        refine ⟨2299663168757834928337361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1533108779171889952224907 2299663168757834928337361)
        ·
          refine ⟨1724747376568376196253021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2299663168757834928337361 1724747376568376196253021)
          ·
            refine ⟨646780266213141073594883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1724747376568376196253021 646780266213141073594883)
            ·
              refine ⟨970170399319711610392325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646780266213141073594883 970170399319711610392325)
              ·
                refine ⟨181906949872445926948561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 970170399319711610392325 181906949872445926948561)
                ·
                  refine ⟨136430212404334445211421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 181906949872445926948561 136430212404334445211421)
                  ·
                    rfl

theorem cell20_298909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_298909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298909 prefixEnd_298909 := by exact prefixLift 298909
  have htrace : WordTrace (prefixWord ++ tailWord_298909) baseStart_298909 baseEnd_298909 := by
    simpa [prefixWord, tailWord_298909, baseEnd_298909] using wordTrace_append hprefix tailTrace_298909
  have hstable : (prefixWord ++ tailWord_298909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298909).length < 2 ^ (prefixWord ++ tailWord_298909).sum := by decide
  have hdescent : baseEnd_298909 < baseStart_298909 := by decide
  rcases family_descends (prefixWord ++ tailWord_298909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298937 : List Nat := [1, 2, 1, 4, 2, 1, 5, 4]
def baseStart_298937 : Nat := 118140960795 + 298937 * 2 ^ 59
def prefixEnd_298937 : Nat := 4983230072969 + 3 ^ 40 * 298937 * 2
def baseEnd_298937 : Nat := 45480997455763597425991

theorem tailTrace_298937 : CollatzResearch.WordTrace tailWord_298937 prefixEnd_298937 45480997455763597425991 := by
  unfold tailWord_298937
  simp only [CollatzResearch.WordTrace]
  refine ⟨10903128118009778220063065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7268752078673185480042043 10903128118009778220063065)
  ·
    refine ⟨8177346088507333665047299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10903128118009778220063065 8177346088507333665047299)
    ·
      refine ⟨12266019132761000497570949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8177346088507333665047299 12266019132761000497570949)
      ·
        refine ⟨2299878587392687593294553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12266019132761000497570949 2299878587392687593294553)
        ·
          refine ⟨1724908940544515694970915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2299878587392687593294553 1724908940544515694970915)
          ·
            refine ⟨2587363410816773542456373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1724908940544515694970915 2587363410816773542456373)
            ·
              refine ⟨242565319764072519605285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2587363410816773542456373 242565319764072519605285)
              ·
                refine ⟨45480997455763597425991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 242565319764072519605285 45480997455763597425991)
                ·
                  rfl

theorem cell20_298937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 4].length) (baseStart_298937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298937 prefixEnd_298937 := by exact prefixLift 298937
  have htrace : WordTrace (prefixWord ++ tailWord_298937) baseStart_298937 baseEnd_298937 := by
    simpa [prefixWord, tailWord_298937, baseEnd_298937] using wordTrace_append hprefix tailTrace_298937
  have hstable : (prefixWord ++ tailWord_298937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298937).length < 2 ^ (prefixWord ++ tailWord_298937).sum := by decide
  have hdescent : baseEnd_298937 < baseStart_298937 := by decide
  rcases family_descends (prefixWord ++ tailWord_298937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298958 : List Nat := [4, 1, 1, 1, 2, 2, 9]
def baseStart_298958 : Nat := 118140960795 + 298958 * 2 ^ 59
def prefixEnd_298958 : Nat := 4983230072969 + 3 ^ 40 * 298958 * 2
def baseEnd_298958 : Nat := 15161397482167561397543

theorem tailTrace_298958 : CollatzResearch.WordTrace tailWord_298958 prefixEnd_298958 15161397482167561397543 := by
  unfold tailWord_298958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1362986756366712350822191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7269262700622465871051685 1362986756366712350822191)
  ·
    refine ⟨2044480134550068526233287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1362986756366712350822191 2044480134550068526233287)
    ·
      refine ⟨3066720201825102789349931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2044480134550068526233287 3066720201825102789349931)
      ·
        refine ⟨4600080302737654184024897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3066720201825102789349931 4600080302737654184024897)
        ·
          refine ⟨3450060227053240638018673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4600080302737654184024897 3450060227053240638018673)
          ·
            refine ⟨2587545170289930478514005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3450060227053240638018673 2587545170289930478514005)
            ·
              refine ⟨15161397482167561397543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2587545170289930478514005 15161397482167561397543)
              ·
                rfl

theorem cell20_298958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 9].length) (baseStart_298958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298958 prefixEnd_298958 := by exact prefixLift 298958
  have htrace : WordTrace (prefixWord ++ tailWord_298958) baseStart_298958 baseEnd_298958 := by
    simpa [prefixWord, tailWord_298958, baseEnd_298958] using wordTrace_append hprefix tailTrace_298958
  have hstable : (prefixWord ++ tailWord_298958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298958).length < 2 ^ (prefixWord ++ tailWord_298958).sum := by decide
  have hdescent : baseEnd_298958 < baseStart_298958 := by decide
  rcases family_descends (prefixWord ++ tailWord_298958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298968 : List Nat := [2, 1, 2, 2, 2, 2, 1, 6, 2]
def baseStart_298968 : Nat := 118140960795 + 298968 * 2 ^ 59
def prefixEnd_298968 : Nat := 4983230072969 + 3 ^ 40 * 298968 * 2
def baseEnd_298968 : Nat := 136457141611992462244513

theorem tailTrace_298968 : CollatzResearch.WordTrace tailWord_298968 prefixEnd_298968 136457141611992462244513 := by
  unfold tailWord_298968
  simp only [CollatzResearch.WordTrace]
  refine ⟨5452129390448735257220779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7269505853931647009627705 5452129390448735257220779)
  ·
    refine ⟨8178194085673102885831169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5452129390448735257220779 8178194085673102885831169)
    ·
      refine ⟨6133645564254827164373377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8178194085673102885831169 6133645564254827164373377)
      ·
        refine ⟨4600234173191120373280033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6133645564254827164373377 4600234173191120373280033)
        ·
          refine ⟨3450175629893340279960025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4600234173191120373280033 3450175629893340279960025)
          ·
            refine ⟨2587631722420005209970019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3450175629893340279960025 2587631722420005209970019)
            ·
              refine ⟨3881447583630007814955029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2587631722420005209970019 3881447583630007814955029)
              ·
                refine ⟨181942855482656616326017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3881447583630007814955029 181942855482656616326017)
                ·
                  refine ⟨136457141611992462244513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 181942855482656616326017 136457141611992462244513)
                  ·
                    rfl

theorem cell20_298968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 6, 2].length) (baseStart_298968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298968 prefixEnd_298968 := by exact prefixLift 298968
  have htrace : WordTrace (prefixWord ++ tailWord_298968) baseStart_298968 baseEnd_298968 := by
    simpa [prefixWord, tailWord_298968, baseEnd_298968] using wordTrace_append hprefix tailTrace_298968
  have hstable : (prefixWord ++ tailWord_298968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298968).length < 2 ^ (prefixWord ++ tailWord_298968).sum := by decide
  have hdescent : baseEnd_298968 < baseStart_298968 := by decide
  rcases family_descends (prefixWord ++ tailWord_298968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299003 : List Nat := [1, 1, 1, 1, 1, 3, 5, 2, 5]
def baseStart_299003 : Nat := 118140960795 + 299003 * 2 ^ 59
def prefixEnd_299003 : Nat := 4983230072969 + 3 ^ 40 * 299003 * 2
def baseEnd_299003 : Nat := 136473116565687896077703

theorem tailTrace_299003 : CollatzResearch.WordTrace tailWord_299003 prefixEnd_299003 136473116565687896077703 := by
  unfold tailWord_299003
  simp only [CollatzResearch.WordTrace]
  refine ⟨10905535335770671491965663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7270356890513780994643775 10905535335770671491965663)
  ·
    refine ⟨16358303003656007237948495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10905535335770671491965663 16358303003656007237948495)
    ·
      refine ⟨24537454505484010856922743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16358303003656007237948495 24537454505484010856922743)
      ·
        refine ⟨36806181758226016285384115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24537454505484010856922743 36806181758226016285384115)
        ·
          refine ⟨55209272637339024428076173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36806181758226016285384115 55209272637339024428076173)
          ·
            refine ⟨20703477239002134160528565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55209272637339024428076173 20703477239002134160528565)
            ·
              refine ⟨1940950991156450077549553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20703477239002134160528565 1940950991156450077549553)
              ·
                refine ⟨1455713243367337558162165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1940950991156450077549553 1455713243367337558162165)
                ·
                  refine ⟨136473116565687896077703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1455713243367337558162165 136473116565687896077703)
                  ·
                    rfl

theorem cell20_299003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 5].length) (baseStart_299003 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299003 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299003 prefixEnd_299003 := by exact prefixLift 299003
  have htrace : WordTrace (prefixWord ++ tailWord_299003) baseStart_299003 baseEnd_299003 := by
    simpa [prefixWord, tailWord_299003, baseEnd_299003] using wordTrace_append hprefix tailTrace_299003
  have hstable : (prefixWord ++ tailWord_299003).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299003).length < 2 ^ (prefixWord ++ tailWord_299003).sum := by decide
  have hdescent : baseEnd_299003 < baseStart_299003 := by decide
  rcases family_descends (prefixWord ++ tailWord_299003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299020 : List Nat := [2, 2, 1, 2, 3, 1, 2, 4, 3]
def baseStart_299020 : Nat := 118140960795 + 299020 * 2 ^ 59
def prefixEnd_299020 : Nat := 4983230072969 + 3 ^ 40 * 299020 * 2
def baseEnd_299020 : Nat := 136480875828911392510967

theorem tailTrace_299020 : CollatzResearch.WordTrace tailWord_299020 prefixEnd_299020 136480875828911392510967 := by
  unfold tailWord_299020
  simp only [CollatzResearch.WordTrace]
  refine ⟨5453077688354541697667257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7270770251139388930223009 5453077688354541697667257)
  ·
    refine ⟨4089808266265906273250443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5453077688354541697667257 4089808266265906273250443)
    ·
      refine ⟨6134712399398859409875665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4089808266265906273250443 6134712399398859409875665)
      ·
        refine ⟨4601034299549144557406749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6134712399398859409875665 4601034299549144557406749)
        ·
          refine ⟨1725387862330929209027531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4601034299549144557406749 1725387862330929209027531)
          ·
            refine ⟨2588081793496393813541297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1725387862330929209027531 2588081793496393813541297)
            ·
              refine ⟨1941061345122295360155973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2588081793496393813541297 1941061345122295360155973)
              ·
                refine ⟨363949002210430380029245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1941061345122295360155973 363949002210430380029245)
                ·
                  refine ⟨136480875828911392510967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 363949002210430380029245 136480875828911392510967)
                  ·
                    rfl

theorem cell20_299020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_299020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299020 prefixEnd_299020 := by exact prefixLift 299020
  have htrace : WordTrace (prefixWord ++ tailWord_299020) baseStart_299020 baseEnd_299020 := by
    simpa [prefixWord, tailWord_299020, baseEnd_299020] using wordTrace_append hprefix tailTrace_299020
  have hstable : (prefixWord ++ tailWord_299020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299020).length < 2 ^ (prefixWord ++ tailWord_299020).sum := by decide
  have hdescent : baseEnd_299020 < baseStart_299020 := by decide
  rcases family_descends (prefixWord ++ tailWord_299020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299027 : List Nat := [1, 1, 1, 2, 1, 4, 5, 1, 4]
def baseStart_299027 : Nat := 118140960795 + 299027 * 2 ^ 59
def prefixEnd_299027 : Nat := 4983230072969 + 3 ^ 40 * 299027 * 2
def baseEnd_299027 : Nat := 136484070819650479277605

theorem tailTrace_299027 : CollatzResearch.WordTrace tailWord_299027 prefixEnd_299027 136484070819650479277605 := by
  unfold tailWord_299027
  simp only [CollatzResearch.WordTrace]
  refine ⟨10906410687683723590839335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7270940458455815727226223 10906410687683723590839335)
  ·
    refine ⟨16359616031525585386259003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10906410687683723590839335 16359616031525585386259003)
    ·
      refine ⟨24539424047288378079388505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16359616031525585386259003 24539424047288378079388505)
      ·
        refine ⟨18404568035466283559541379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24539424047288378079388505 18404568035466283559541379)
        ·
          refine ⟨27606852053199425339312069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18404568035466283559541379 27606852053199425339312069)
          ·
            refine ⟨5176284759974892251121013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27606852053199425339312069 5176284759974892251121013)
            ·
              refine ⟨485276696247646148542595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5176284759974892251121013 485276696247646148542595)
              ·
                refine ⟨727915044371469222813893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 485276696247646148542595 727915044371469222813893)
                ·
                  refine ⟨136484070819650479277605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 727915044371469222813893 136484070819650479277605)
                  ·
                    rfl

theorem cell20_299027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 4].length) (baseStart_299027 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299027 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299027 prefixEnd_299027 := by exact prefixLift 299027
  have htrace : WordTrace (prefixWord ++ tailWord_299027) baseStart_299027 baseEnd_299027 := by
    simpa [prefixWord, tailWord_299027, baseEnd_299027] using wordTrace_append hprefix tailTrace_299027
  have hstable : (prefixWord ++ tailWord_299027).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299027).length < 2 ^ (prefixWord ++ tailWord_299027).sum := by decide
  have hdescent : baseEnd_299027 < baseStart_299027 := by decide
  rcases family_descends (prefixWord ++ tailWord_299027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299034 : List Nat := [3, 1, 1, 3, 1, 3, 1, 7]
def baseStart_299034 : Nat := 118140960795 + 299034 * 2 ^ 59
def prefixEnd_299034 : Nat := 4983230072969 + 3 ^ 40 * 299034 * 2
def baseEnd_299034 : Nat := 45495755270129855348081

theorem tailTrace_299034 : CollatzResearch.WordTrace tailWord_299034 prefixEnd_299034 45495755270129855348081 := by
  unfold tailWord_299034
  simp only [CollatzResearch.WordTrace]
  refine ⟨2726666499664590946586039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7271110665772242524229437 2726666499664590946586039)
  ·
    refine ⟨4089999749496886419879059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2726666499664590946586039 4089999749496886419879059)
    ·
      refine ⟨6134999624245329629818589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4089999749496886419879059 6134999624245329629818589)
      ·
        refine ⟨2300624859091998611181971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6134999624245329629818589 2300624859091998611181971)
        ·
          refine ⟨3450937288637997916772957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2300624859091998611181971 3450937288637997916772957)
          ·
            refine ⟨1294101483239249218789859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3450937288637997916772957 1294101483239249218789859)
            ·
              refine ⟨1941152224858873828184789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1294101483239249218789859 1941152224858873828184789)
              ·
                refine ⟨45495755270129855348081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1941152224858873828184789 45495755270129855348081)
                ·
                  rfl

theorem cell20_299034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_299034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299034 prefixEnd_299034 := by exact prefixLift 299034
  have htrace : WordTrace (prefixWord ++ tailWord_299034) baseStart_299034 baseEnd_299034 := by
    simpa [prefixWord, tailWord_299034, baseEnd_299034] using wordTrace_append hprefix tailTrace_299034
  have hstable : (prefixWord ++ tailWord_299034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299034).length < 2 ^ (prefixWord ++ tailWord_299034).sum := by decide
  have hdescent : baseEnd_299034 < baseStart_299034 := by decide
  rcases family_descends (prefixWord ++ tailWord_299034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299037 : List Nat := [1, 4, 2, 2, 2, 2, 1, 3, 3]
def baseStart_299037 : Nat := 118140960795 + 299037 * 2 ^ 59
def prefixEnd_299037 : Nat := 4983230072969 + 3 ^ 40 * 299037 * 2
def baseEnd_299037 : Nat := 136488635092134888944231

theorem tailTrace_299037 : CollatzResearch.WordTrace tailWord_299037 prefixEnd_299037 136488635092134888944231 := by
  unfold tailWord_299037
  simp only [CollatzResearch.WordTrace]
  refine ⟨10906775417647495298703365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7271183611764996865802243 10906775417647495298703365)
  ·
    refine ⟨2045020390808905368506881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10906775417647495298703365 2045020390808905368506881)
    ·
      refine ⟨1533765293106679026380161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2045020390808905368506881 1533765293106679026380161)
      ·
        refine ⟨1150323969830009269785121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1533765293106679026380161 1150323969830009269785121)
        ·
          refine ⟨862742977372506952338841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1150323969830009269785121 862742977372506952338841)
          ·
            refine ⟨647057233029380214254131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 862742977372506952338841 647057233029380214254131)
            ·
              refine ⟨970585849544070321381197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 647057233029380214254131 970585849544070321381197)
              ·
                refine ⟨363969693579026370517949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 970585849544070321381197 363969693579026370517949)
                ·
                  refine ⟨136488635092134888944231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 363969693579026370517949 136488635092134888944231)
                  ·
                    rfl

theorem cell20_299037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_299037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299037 prefixEnd_299037 := by exact prefixLift 299037
  have htrace : WordTrace (prefixWord ++ tailWord_299037) baseStart_299037 baseEnd_299037 := by
    simpa [prefixWord, tailWord_299037, baseEnd_299037] using wordTrace_append hprefix tailTrace_299037
  have hstable : (prefixWord ++ tailWord_299037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299037).length < 2 ^ (prefixWord ++ tailWord_299037).sum := by decide
  have hdescent : baseEnd_299037 < baseStart_299037 := by decide
  rcases family_descends (prefixWord ++ tailWord_299037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299078 : List Nat := [6, 1, 1, 1, 1, 1, 3, 4, 2]
def baseStart_299078 : Nat := 118140960795 + 299078 * 2 ^ 59
def prefixEnd_299078 : Nat := 4983230072969 + 3 ^ 40 * 299078 * 2
def baseEnd_299078 : Nat := 136507348609320968577397

theorem tailTrace_299078 : CollatzResearch.WordTrace tailWord_299078 prefixEnd_299078 136507348609320968577397 := by
  unfold tailWord_299078
  simp only [CollatzResearch.WordTrace]
  refine ⟨340883462828092478154559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7272180540332639533963925 340883462828092478154559)
  ·
    refine ⟨511325194242138717231839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 340883462828092478154559 511325194242138717231839)
    ·
      refine ⟨766987791363208075847759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 511325194242138717231839 766987791363208075847759)
      ·
        refine ⟨1150481687044812113771639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 766987791363208075847759 1150481687044812113771639)
        ·
          refine ⟨1725722530567218170657459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1150481687044812113771639 1725722530567218170657459)
          ·
            refine ⟨2588583795850827255986189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1725722530567218170657459 2588583795850827255986189)
            ·
              refine ⟨970718923444060220994821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2588583795850827255986189 970718923444060220994821)
              ·
                refine ⟨182009798145761291436529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 970718923444060220994821 182009798145761291436529)
                ·
                  refine ⟨136507348609320968577397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182009798145761291436529 136507348609320968577397)
                  ·
                    rfl

theorem cell20_299078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_299078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299078 prefixEnd_299078 := by exact prefixLift 299078
  have htrace : WordTrace (prefixWord ++ tailWord_299078) baseStart_299078 baseEnd_299078 := by
    simpa [prefixWord, tailWord_299078, baseEnd_299078] using wordTrace_append hprefix tailTrace_299078
  have hstable : (prefixWord ++ tailWord_299078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299078).length < 2 ^ (prefixWord ++ tailWord_299078).sum := by decide
  have hdescent : baseEnd_299078 < baseStart_299078 := by decide
  rcases family_descends (prefixWord ++ tailWord_299078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299096 : List Nat := [2, 1, 2, 2, 1, 4, 2, 3, 3]
def baseStart_299096 : Nat := 118140960795 + 299096 * 2 ^ 59
def prefixEnd_299096 : Nat := 4983230072969 + 3 ^ 40 * 299096 * 2
def baseEnd_299096 : Nat := 136515564299792905977323

theorem tailTrace_299096 : CollatzResearch.WordTrace tailWord_299096 prefixEnd_299096 136515564299792905977323 := by
  unfold tailWord_299096
  simp only [CollatzResearch.WordTrace]
  refine ⟨5454463662216874187550571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7272618216289165583400761 5454463662216874187550571)
  ·
    refine ⟨8181695493325311281325857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5454463662216874187550571 8181695493325311281325857)
    ·
      refine ⟨6136271619993983460994393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8181695493325311281325857 6136271619993983460994393)
      ·
        refine ⟨4602203714995487595745795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6136271619993983460994393 4602203714995487595745795)
        ·
          refine ⟨6903305572493231393618693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4602203714995487595745795 6903305572493231393618693)
          ·
            refine ⟨1294369794842480886303505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6903305572493231393618693 1294369794842480886303505)
            ·
              refine ⟨970777346131860664727629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1294369794842480886303505 970777346131860664727629)
              ·
                refine ⟨364041504799447749272861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 970777346131860664727629 364041504799447749272861)
                ·
                  refine ⟨136515564299792905977323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 364041504799447749272861 136515564299792905977323)
                  ·
                    rfl

theorem cell20_299096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 3].length) (baseStart_299096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299096 prefixEnd_299096 := by exact prefixLift 299096
  have htrace : WordTrace (prefixWord ++ tailWord_299096) baseStart_299096 baseEnd_299096 := by
    simpa [prefixWord, tailWord_299096, baseEnd_299096] using wordTrace_append hprefix tailTrace_299096
  have hstable : (prefixWord ++ tailWord_299096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299096).length < 2 ^ (prefixWord ++ tailWord_299096).sum := by decide
  have hdescent : baseEnd_299096 < baseStart_299096 := by decide
  rcases family_descends (prefixWord ++ tailWord_299096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299102 : List Nat := [4, 4, 1, 1, 2, 1, 3, 4]
def baseStart_299102 : Nat := 118140960795 + 299102 * 2 ^ 59
def prefixEnd_299102 : Nat := 4983230072969 + 3 ^ 40 * 299102 * 2
def baseEnd_299102 : Nat := 45506100954427850592433

theorem tailTrace_299102 : CollatzResearch.WordTrace tailWord_299102 prefixEnd_299102 45506100954427850592433 := by
  unfold tailWord_299102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1363643270301501424977445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7272764108274674266546373 1363643270301501424977445)
  ·
    refine ⟨255683113181531517183271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1363643270301501424977445 255683113181531517183271)
    ·
      refine ⟨383524669772297275774907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255683113181531517183271 383524669772297275774907)
      ·
        refine ⟨575287004658445913662361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383524669772297275774907 575287004658445913662361)
        ·
          refine ⟨431465253493834435246771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 575287004658445913662361 431465253493834435246771)
          ·
            refine ⟨647197880240751652870157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431465253493834435246771 647197880240751652870157)
            ·
              refine ⟨242699205090281869826309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 647197880240751652870157 242699205090281869826309)
              ·
                refine ⟨45506100954427850592433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 242699205090281869826309 45506100954427850592433)
                ·
                  rfl

theorem cell20_299102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_299102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299102 prefixEnd_299102 := by exact prefixLift 299102
  have htrace : WordTrace (prefixWord ++ tailWord_299102) baseStart_299102 baseEnd_299102 := by
    simpa [prefixWord, tailWord_299102, baseEnd_299102] using wordTrace_append hprefix tailTrace_299102
  have hstable : (prefixWord ++ tailWord_299102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299102).length < 2 ^ (prefixWord ++ tailWord_299102).sum := by decide
  have hdescent : baseEnd_299102 < baseStart_299102 := by decide
  rcases family_descends (prefixWord ++ tailWord_299102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299120 : List Nat := [2, 1, 1, 1, 5, 2, 1, 5, 2]
def baseStart_299120 : Nat := 118140960795 + 299120 * 2 ^ 59
def prefixEnd_299120 : Nat := 4983230072969 + 3 ^ 40 * 299120 * 2
def baseEnd_299120 : Nat := 136526518553755489177225

theorem tailTrace_299120 : CollatzResearch.WordTrace tailWord_299120 prefixEnd_299120 136526518553755489177225 := by
  unfold tailWord_299120
  simp only [CollatzResearch.WordTrace]
  refine ⟨5454901338173400236987407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7273201784231200315983209 5454901338173400236987407)
  ·
    refine ⟨8182352007260100355481111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5454901338173400236987407 8182352007260100355481111)
    ·
      refine ⟨12273528010890150533221667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8182352007260100355481111 12273528010890150533221667)
      ·
        refine ⟨18410292016335225799832501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12273528010890150533221667 18410292016335225799832501)
        ·
          refine ⟨1725964876531427418734297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18410292016335225799832501 1725964876531427418734297)
          ·
            refine ⟨1294473657398570564050723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1725964876531427418734297 1294473657398570564050723)
            ·
              refine ⟨1941710486097855846076085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1294473657398570564050723 1941710486097855846076085)
              ·
                refine ⟨182035358071673985569633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1941710486097855846076085 182035358071673985569633)
                ·
                  refine ⟨136526518553755489177225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182035358071673985569633 136526518553755489177225)
                  ·
                    rfl

theorem cell20_299120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 5, 2].length) (baseStart_299120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299120 prefixEnd_299120 := by exact prefixLift 299120
  have htrace : WordTrace (prefixWord ++ tailWord_299120) baseStart_299120 baseEnd_299120 := by
    simpa [prefixWord, tailWord_299120, baseEnd_299120] using wordTrace_append hprefix tailTrace_299120
  have hstable : (prefixWord ++ tailWord_299120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299120).length < 2 ^ (prefixWord ++ tailWord_299120).sum := by decide
  have hdescent : baseEnd_299120 < baseStart_299120 := by decide
  rcases family_descends (prefixWord ++ tailWord_299120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299141 : List Nat := [1, 3, 1, 1, 5, 1, 1, 3, 4]
def baseStart_299141 : Nat := 118140960795 + 299141 * 2 ^ 59
def prefixEnd_299141 : Nat := 4983230072969 + 3 ^ 40 * 299141 * 2
def baseEnd_299141 : Nat := 136536103525972749477139

theorem tailTrace_299141 : CollatzResearch.WordTrace tailWord_299141 prefixEnd_299141 136536103525972749477139 := by
  unfold tailWord_299141
  simp only [CollatzResearch.WordTrace]
  refine ⟨10910568609270721060489277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7273712406180480706992851 10910568609270721060489277)
  ·
    refine ⟨4091463228476520397683479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10910568609270721060489277 4091463228476520397683479)
    ·
      refine ⟨6137194842714780596525219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4091463228476520397683479 6137194842714780596525219)
      ·
        refine ⟨9205792264072170894787829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6137194842714780596525219 9205792264072170894787829)
        ·
          refine ⟨863043024756766021386359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9205792264072170894787829 863043024756766021386359)
          ·
            refine ⟨1294564537135149032079539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 863043024756766021386359 1294564537135149032079539)
            ·
              refine ⟨1941846805702723548119309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1294564537135149032079539 1941846805702723548119309)
              ·
                refine ⟨728192552138521330544741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1941846805702723548119309 728192552138521330544741)
                ·
                  refine ⟨136536103525972749477139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 728192552138521330544741 136536103525972749477139)
                  ·
                    rfl

theorem cell20_299141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_299141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299141 prefixEnd_299141 := by exact prefixLift 299141
  have htrace : WordTrace (prefixWord ++ tailWord_299141) baseStart_299141 baseEnd_299141 := by
    simpa [prefixWord, tailWord_299141, baseEnd_299141] using wordTrace_append hprefix tailTrace_299141
  have hstable : (prefixWord ++ tailWord_299141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299141).length < 2 ^ (prefixWord ++ tailWord_299141).sum := by decide
  have hdescent : baseEnd_299141 < baseStart_299141 := by decide
  rcases family_descends (prefixWord ++ tailWord_299141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299165 : List Nat := [1, 4, 2, 1, 1, 3, 4, 4]
def baseStart_299165 : Nat := 118140960795 + 299165 * 2 ^ 59
def prefixEnd_299165 : Nat := 4983230072969 + 3 ^ 40 * 299165 * 2
def baseEnd_299165 : Nat := 45515685926645110892347

theorem tailTrace_299165 : CollatzResearch.WordTrace tailWord_299165 prefixEnd_299165 45515685926645110892347 := by
  unfold tailWord_299165
  simp only [CollatzResearch.WordTrace]
  refine ⟨10911443961183773159362949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7274295974122515439575299 10911443961183773159362949)
  ·
    refine ⟨2045895742721957467380553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10911443961183773159362949 2045895742721957467380553)
    ·
      refine ⟨1534421807041468100535415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2045895742721957467380553 1534421807041468100535415)
      ·
        refine ⟨2301632710562202150803123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1534421807041468100535415 2301632710562202150803123)
        ·
          refine ⟨3452449065843303226204685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2301632710562202150803123 3452449065843303226204685)
          ·
            refine ⟨1294668399691238709826757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3452449065843303226204685 1294668399691238709826757)
            ·
              refine ⟨242750324942107258092517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1294668399691238709826757 242750324942107258092517)
              ·
                refine ⟨45515685926645110892347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 242750324942107258092517 45515685926645110892347)
                ·
                  rfl

theorem cell20_299165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 4].length) (baseStart_299165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299165 prefixEnd_299165 := by exact prefixLift 299165
  have htrace : WordTrace (prefixWord ++ tailWord_299165) baseStart_299165 baseEnd_299165 := by
    simpa [prefixWord, tailWord_299165, baseEnd_299165] using wordTrace_append hprefix tailTrace_299165
  have hstable : (prefixWord ++ tailWord_299165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299165).length < 2 ^ (prefixWord ++ tailWord_299165).sum := by decide
  have hdescent : baseEnd_299165 < baseStart_299165 := by decide
  rcases family_descends (prefixWord ++ tailWord_299165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299188 : List Nat := [2, 5, 3, 1, 2, 1, 1, 1, 4]
def baseStart_299188 : Nat := 118140960795 + 299188 * 2 ^ 59
def prefixEnd_299188 : Nat := 4983230072969 + 3 ^ 40 * 299188 * 2
def baseEnd_299188 : Nat := 136557555606649474910281

theorem tailTrace_299188 : CollatzResearch.WordTrace tailWord_299188 prefixEnd_299188 136557555606649474910281 := by
  unfold tailWord_299188
  simp only [CollatzResearch.WordTrace]
  refine ⟨5456141420050224043725109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7274855226733632058300145 5456141420050224043725109)
  ·
    refine ⟨511513258129708504099229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5456141420050224043725109 511513258129708504099229)
    ·
      refine ⟨191817471798640689037211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 511513258129708504099229 191817471798640689037211)
      ·
        refine ⟨287726207697961033555817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191817471798640689037211 287726207697961033555817)
        ·
          refine ⟨215794655773470775166863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287726207697961033555817 215794655773470775166863)
          ·
            refine ⟨323691983660206162750295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215794655773470775166863 323691983660206162750295)
            ·
              refine ⟨485537975490309244125443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323691983660206162750295 485537975490309244125443)
              ·
                refine ⟨728306963235463866188165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 485537975490309244125443 728306963235463866188165)
                ·
                  refine ⟨136557555606649474910281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 728306963235463866188165 136557555606649474910281)
                  ·
                    rfl

theorem cell20_299188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_299188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299188 prefixEnd_299188 := by exact prefixLift 299188
  have htrace : WordTrace (prefixWord ++ tailWord_299188) baseStart_299188 baseEnd_299188 := by
    simpa [prefixWord, tailWord_299188, baseEnd_299188] using wordTrace_append hprefix tailTrace_299188
  have hstable : (prefixWord ++ tailWord_299188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299188).length < 2 ^ (prefixWord ++ tailWord_299188).sum := by decide
  have hdescent : baseEnd_299188 < baseStart_299188 := by decide
  rcases family_descends (prefixWord ++ tailWord_299188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299193 : List Nat := [1, 2, 1, 4, 1, 2, 1, 3, 5]
def baseStart_299193 : Nat := 118140960795 + 299193 * 2 ^ 59
def prefixEnd_299193 : Nat := 4983230072969 + 3 ^ 40 * 299193 * 2
def baseEnd_299193 : Nat := 136559837742891679743593

theorem tailTrace_299193 : CollatzResearch.WordTrace tailWord_299193 prefixEnd_299193 136559837742891679743593 := by
  unfold tailWord_299193
  simp only [CollatzResearch.WordTrace]
  refine ⟨10912465205082333941382233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7274976803388222627588155 10912465205082333941382233)
  ·
    refine ⟨8184348903811750456036675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10912465205082333941382233 8184348903811750456036675)
    ·
      refine ⟨12276523355717625684055013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8184348903811750456036675 12276523355717625684055013)
      ·
        refine ⟨2301848129197054815760315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12276523355717625684055013 2301848129197054815760315)
        ·
          refine ⟨3452772193795582223640473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2301848129197054815760315 3452772193795582223640473)
          ·
            refine ⟨2589579145346686667730355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3452772193795582223640473 2589579145346686667730355)
            ·
              refine ⟨3884368718020030001595533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2589579145346686667730355 3884368718020030001595533)
              ·
                refine ⟨1456638269257511250598325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3884368718020030001595533 1456638269257511250598325)
                ·
                  refine ⟨136559837742891679743593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1456638269257511250598325 136559837742891679743593)
                  ·
                    rfl

theorem cell20_299193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_299193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299193 prefixEnd_299193 := by exact prefixLift 299193
  have htrace : WordTrace (prefixWord ++ tailWord_299193) baseStart_299193 baseEnd_299193 := by
    simpa [prefixWord, tailWord_299193, baseEnd_299193] using wordTrace_append hprefix tailTrace_299193
  have hstable : (prefixWord ++ tailWord_299193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299193).length < 2 ^ (prefixWord ++ tailWord_299193).sum := by decide
  have hdescent : baseEnd_299193 < baseStart_299193 := by decide
  rcases family_descends (prefixWord ++ tailWord_299193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299202 : List Nat := [3, 5, 1, 1, 1, 3, 2, 1, 3]
def baseStart_299202 : Nat := 118140960795 + 299202 * 2 ^ 59
def prefixEnd_299202 : Nat := 4983230072969 + 3 ^ 40 * 299202 * 2
def baseEnd_299202 : Nat := 136563945588127648443557

theorem tailTrace_299202 : CollatzResearch.WordTrace tailWord_299202 prefixEnd_299202 136563945588127648443557 := by
  unfold tailWord_299202
  simp only [CollatzResearch.WordTrace]
  refine ⟨2728198365512432119614965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7275195641366485652306573 2728198365512432119614965)
  ·
    refine ⟨255768596766790511213903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2728198365512432119614965 255768596766790511213903)
    ·
      refine ⟨383652895150185766820855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255768596766790511213903 383652895150185766820855)
      ·
        refine ⟨575479342725278650231283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383652895150185766820855 575479342725278650231283)
        ·
          refine ⟨863219014087917975346925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 575479342725278650231283 863219014087917975346925)
          ·
            refine ⟨323707130282969240755097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 863219014087917975346925 323707130282969240755097)
            ·
              refine ⟨242780347712226930566323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 323707130282969240755097 242780347712226930566323)
              ·
                refine ⟨364170521568340395849485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242780347712226930566323 364170521568340395849485)
                ·
                  refine ⟨136563945588127648443557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 364170521568340395849485 136563945588127648443557)
                  ·
                    rfl

theorem cell20_299202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_299202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299202 prefixEnd_299202 := by exact prefixLift 299202
  have htrace : WordTrace (prefixWord ++ tailWord_299202) baseStart_299202 baseEnd_299202 := by
    simpa [prefixWord, tailWord_299202, baseEnd_299202] using wordTrace_append hprefix tailTrace_299202
  have hstable : (prefixWord ++ tailWord_299202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299202).length < 2 ^ (prefixWord ++ tailWord_299202).sum := by decide
  have hdescent : baseEnd_299202 < baseStart_299202 := by decide
  rcases family_descends (prefixWord ++ tailWord_299202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299210 : List Nat := [3, 1, 2, 1, 3, 1, 3, 3, 3]
def baseStart_299210 : Nat := 118140960795 + 299210 * 2 ^ 59
def prefixEnd_299210 : Nat := 4983230072969 + 3 ^ 40 * 299210 * 2
def baseEnd_299210 : Nat := 136567597006115176176857

theorem tailTrace_299210 : CollatzResearch.WordTrace tailWord_299210 prefixEnd_299210 136567597006115176176857 := by
  unfold tailWord_299210
  simp only [CollatzResearch.WordTrace]
  refine ⟨2728271311505186461187771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7275390164013830563167389 2728271311505186461187771)
  ·
    refine ⟨4092406967257779691781657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2728271311505186461187771 4092406967257779691781657)
    ·
      refine ⟨3069305225443334768836243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4092406967257779691781657 3069305225443334768836243)
      ·
        refine ⟨4603957838165002153254365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3069305225443334768836243 4603957838165002153254365)
        ·
          refine ⟨1726484189311875807470387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4603957838165002153254365 1726484189311875807470387)
          ·
            refine ⟨2589726283967813711205581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1726484189311875807470387 2589726283967813711205581)
            ·
              refine ⟨971147356487930141702093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2589726283967813711205581 971147356487930141702093)
              ·
                refine ⟨364180258682973803138285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 971147356487930141702093 364180258682973803138285)
                ·
                  refine ⟨136567597006115176176857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 364180258682973803138285 136567597006115176176857)
                  ·
                    rfl

theorem cell20_299210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_299210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299210 prefixEnd_299210 := by exact prefixLift 299210
  have htrace : WordTrace (prefixWord ++ tailWord_299210) baseStart_299210 baseEnd_299210 := by
    simpa [prefixWord, tailWord_299210, baseEnd_299210] using wordTrace_append hprefix tailTrace_299210
  have hstable : (prefixWord ++ tailWord_299210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299210).length < 2 ^ (prefixWord ++ tailWord_299210).sum := by decide
  have hdescent : baseEnd_299210 < baseStart_299210 := by decide
  rcases family_descends (prefixWord ++ tailWord_299210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299224 : List Nat := [2, 1, 2, 2, 4, 1, 2, 6]
def baseStart_299224 : Nat := 118140960795 + 299224 * 2 ^ 59
def prefixEnd_299224 : Nat := 4983230072969 + 3 ^ 40 * 299224 * 2
def baseEnd_299224 : Nat := 45524662329197783236711

theorem tailTrace_299224 : CollatzResearch.WordTrace tailWord_299224 prefixEnd_299224 45524662329197783236711 := by
  unfold tailWord_299224
  simp only [CollatzResearch.WordTrace]
  refine ⟨5456797933985013117880363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7275730578646684157173817 5456797933985013117880363)
  ·
    refine ⟨8185196900977519676820545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5456797933985013117880363 8185196900977519676820545)
    ·
      refine ⟨6138897675733139757615409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8185196900977519676820545 6138897675733139757615409)
      ·
        refine ⟨4604173256799854818211557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6138897675733139757615409 4604173256799854818211557)
        ·
          refine ⟨863282485649972778414667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4604173256799854818211557 863282485649972778414667)
          ·
            refine ⟨1294923728474959167622001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 863282485649972778414667 1294923728474959167622001)
            ·
              refine ⟨971192796356219375716501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1294923728474959167622001 971192796356219375716501)
              ·
                refine ⟨45524662329197783236711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 971192796356219375716501 45524662329197783236711)
                ·
                  rfl

theorem cell20_299224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 6].length) (baseStart_299224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299224 prefixEnd_299224 := by exact prefixLift 299224
  have htrace : WordTrace (prefixWord ++ tailWord_299224) baseStart_299224 baseEnd_299224 := by
    simpa [prefixWord, tailWord_299224, baseEnd_299224] using wordTrace_append hprefix tailTrace_299224
  have hstable : (prefixWord ++ tailWord_299224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299224).length < 2 ^ (prefixWord ++ tailWord_299224).sum := by decide
  have hdescent : baseEnd_299224 < baseStart_299224 := by decide
  rcases family_descends (prefixWord ++ tailWord_299224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299283 : List Nat := [1, 1, 1, 2, 1, 3, 1, 10]
def baseStart_299283 : Nat := 118140960795 + 299283 * 2 ^ 59
def prefixEnd_299283 : Nat := 4983230072969 + 3 ^ 40 * 299283 * 2
def baseEnd_299283 : Nat := 45533638731750455581075

theorem tailTrace_299283 : CollatzResearch.WordTrace tailWord_299283 prefixEnd_299283 45533638731750455581075 := by
  unfold tailWord_299283
  simp only [CollatzResearch.WordTrace]
  refine ⟨10915747774756279312158503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7277165183170852874772335 10915747774756279312158503)
  ·
    refine ⟨16373621662134418968237755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10915747774756279312158503 16373621662134418968237755)
    ·
      refine ⟨24560432493201628452356633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16373621662134418968237755 24560432493201628452356633)
      ·
        refine ⟨18420324369901221339267475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24560432493201628452356633 18420324369901221339267475)
        ·
          refine ⟨27630486554851832008901213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18420324369901221339267475 27630486554851832008901213)
          ·
            refine ⟨10361432458069437003337955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27630486554851832008901213 10361432458069437003337955)
            ·
              refine ⟨15542148687104155505006933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10361432458069437003337955 15542148687104155505006933)
              ·
                refine ⟨45533638731750455581075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 15542148687104155505006933 45533638731750455581075)
                ·
                  rfl

theorem cell20_299283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 10].length) (baseStart_299283 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299283 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299283 prefixEnd_299283 := by exact prefixLift 299283
  have htrace : WordTrace (prefixWord ++ tailWord_299283) baseStart_299283 baseEnd_299283 := by
    simpa [prefixWord, tailWord_299283, baseEnd_299283] using wordTrace_append hprefix tailTrace_299283
  have hstable : (prefixWord ++ tailWord_299283).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299283).length < 2 ^ (prefixWord ++ tailWord_299283).sum := by decide
  have hdescent : baseEnd_299283 < baseStart_299283 := by decide
  rcases family_descends (prefixWord ++ tailWord_299283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299300 : List Nat := [2, 3, 1, 3, 1, 3, 7]
def baseStart_299300 : Nat := 118140960795 + 299300 * 2 ^ 59
def prefixEnd_299300 : Nat := 4983230072969 + 3 ^ 40 * 299300 * 2
def baseEnd_299300 : Nat := 15178741717608318130721

theorem tailTrace_299300 : CollatzResearch.WordTrace tailWord_299300 prefixEnd_299300 15178741717608318130721 := by
  unfold tailWord_299300
  simp only [CollatzResearch.WordTrace]
  refine ⟨5458183907847345607763677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7277578543796460810351569 5458183907847345607763677)
  ·
    refine ⟨2046818965442754602911379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5458183907847345607763677 2046818965442754602911379)
    ·
      refine ⟨3070228448164131904367069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2046818965442754602911379 3070228448164131904367069)
      ·
        refine ⟨1151335668061549464137651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3070228448164131904367069 1151335668061549464137651)
        ·
          refine ⟨1727003502092324196206477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1151335668061549464137651 1727003502092324196206477)
          ·
            refine ⟨647626313284621573577429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1727003502092324196206477 647626313284621573577429)
            ·
              refine ⟨15178741717608318130721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 647626313284621573577429 15178741717608318130721)
              ·
                rfl

theorem cell20_299300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 7].length) (baseStart_299300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299300 prefixEnd_299300 := by exact prefixLift 299300
  have htrace : WordTrace (prefixWord ++ tailWord_299300) baseStart_299300 baseEnd_299300 := by
    simpa [prefixWord, tailWord_299300, baseEnd_299300] using wordTrace_append hprefix tailTrace_299300
  have hstable : (prefixWord ++ tailWord_299300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299300).length < 2 ^ (prefixWord ++ tailWord_299300).sum := by decide
  have hdescent : baseEnd_299300 < baseStart_299300 := by decide
  rcases family_descends (prefixWord ++ tailWord_299300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299345 : List Nat := [1, 2, 2, 1, 4, 2, 1, 2, 5]
def baseStart_299345 : Nat := 118140960795 + 299345 * 2 ^ 59
def prefixEnd_299345 : Nat := 4983230072969 + 3 ^ 40 * 299345 * 2
def baseEnd_299345 : Nat := 136629214684654706676305

theorem tailTrace_299345 : CollatzResearch.WordTrace tailWord_299345 prefixEnd_299345 136629214684654706676305 := by
  unfold tailWord_299345
  simp only [CollatzResearch.WordTrace]
  refine ⟨10918009100531663900915489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7278672733687775933943659 10918009100531663900915489)
  ·
    refine ⟨8188506825398747925686617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10918009100531663900915489 8188506825398747925686617)
    ·
      refine ⟨6141380119049060944264963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8188506825398747925686617 6141380119049060944264963)
      ·
        refine ⟨9212070178573591416397445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6141380119049060944264963 9212070178573591416397445)
        ·
          refine ⟨1727263158482548390574521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9212070178573591416397445 1727263158482548390574521)
          ·
            refine ⟨1295447368861911292930891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1727263158482548390574521 1295447368861911292930891)
            ·
              refine ⟨1943171053292866939396337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1295447368861911292930891 1943171053292866939396337)
              ·
                refine ⟨1457378289969650204547253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1943171053292866939396337 1457378289969650204547253)
                ·
                  refine ⟨136629214684654706676305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1457378289969650204547253 136629214684654706676305)
                  ·
                    rfl

theorem cell20_299345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_299345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299345 prefixEnd_299345 := by exact prefixLift 299345
  have htrace : WordTrace (prefixWord ++ tailWord_299345) baseStart_299345 baseEnd_299345 := by
    simpa [prefixWord, tailWord_299345, baseEnd_299345] using wordTrace_append hprefix tailTrace_299345
  have hstable : (prefixWord ++ tailWord_299345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299345).length < 2 ^ (prefixWord ++ tailWord_299345).sum := by decide
  have hdescent : baseEnd_299345 < baseStart_299345 := by decide
  rcases family_descends (prefixWord ++ tailWord_299345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299359 : List Nat := [1, 1, 2, 3, 1, 2, 10]
def baseStart_299359 : Nat := 118140960795 + 299359 * 2 ^ 59
def prefixEnd_299359 : Nat := 4983230072969 + 3 ^ 40 * 299359 * 2
def baseEnd_299359 : Nat := 15181733851792542245509

theorem tailTrace_299359 : CollatzResearch.WordTrace tailWord_299359 prefixEnd_299359 15181733851792542245509 := by
  unfold tailWord_299359
  simp only [CollatzResearch.WordTrace]
  refine ⟨10918519722480944291925131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7279013148320629527950087 10918519722480944291925131)
  ·
    refine ⟨16377779583721416437887697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10918519722480944291925131 16377779583721416437887697)
    ·
      refine ⟨12283334687791062328415773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16377779583721416437887697 12283334687791062328415773)
      ·
        refine ⟨4606250507921648373155915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12283334687791062328415773 4606250507921648373155915)
        ·
          refine ⟨6909375761882472559733873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4606250507921648373155915 6909375761882472559733873)
          ·
            refine ⟨5182031821411854419800405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6909375761882472559733873 5182031821411854419800405)
            ·
              refine ⟨15181733851792542245509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5182031821411854419800405 15181733851792542245509)
              ·
                rfl

theorem cell20_299359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 10].length) (baseStart_299359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299359 prefixEnd_299359 := by exact prefixLift 299359
  have htrace : WordTrace (prefixWord ++ tailWord_299359) baseStart_299359 baseEnd_299359 := by
    simpa [prefixWord, tailWord_299359, baseEnd_299359] using wordTrace_append hprefix tailTrace_299359
  have hstable : (prefixWord ++ tailWord_299359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299359).length < 2 ^ (prefixWord ++ tailWord_299359).sum := by decide
  have hdescent : baseEnd_299359 < baseStart_299359 := by decide
  rcases family_descends (prefixWord ++ tailWord_299359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299362 : List Nat := [3, 3, 2, 1, 1, 2, 2, 1, 5]
def baseStart_299362 : Nat := 118140960795 + 299362 * 2 ^ 59
def prefixEnd_299362 : Nat := 4983230072969 + 3 ^ 40 * 299362 * 2
def baseEnd_299362 : Nat := 136636973947878203109569

theorem tailTrace_299362 : CollatzResearch.WordTrace tailWord_299362 prefixEnd_299362 136636973947878203109569 := by
  unfold tailWord_299362
  simp only [CollatzResearch.WordTrace]
  refine ⟨2729657285367518951071085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7279086094313383869522893 2729657285367518951071085)
  ·
    refine ⟨1023621482012819606651657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2729657285367518951071085 1023621482012819606651657)
    ·
      refine ⟨767716111509614704988743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1023621482012819606651657 767716111509614704988743)
      ·
        refine ⟨1151574167264422057483115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 767716111509614704988743 1151574167264422057483115)
        ·
          refine ⟨1727361250896633086224673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1151574167264422057483115 1727361250896633086224673)
          ·
            refine ⟨1295520938172474814668505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1727361250896633086224673 1295520938172474814668505)
            ·
              refine ⟨971640703629356111001379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1295520938172474814668505 971640703629356111001379)
              ·
                refine ⟨1457461055444034166502069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 971640703629356111001379 1457461055444034166502069)
                ·
                  refine ⟨136636973947878203109569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1457461055444034166502069 136636973947878203109569)
                  ·
                    rfl

theorem cell20_299362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_299362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299362 prefixEnd_299362 := by exact prefixLift 299362
  have htrace : WordTrace (prefixWord ++ tailWord_299362) baseStart_299362 baseEnd_299362 := by
    simpa [prefixWord, tailWord_299362, baseEnd_299362] using wordTrace_append hprefix tailTrace_299362
  have hstable : (prefixWord ++ tailWord_299362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299362).length < 2 ^ (prefixWord ++ tailWord_299362).sum := by decide
  have hdescent : baseEnd_299362 < baseStart_299362 := by decide
  rcases family_descends (prefixWord ++ tailWord_299362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299365 : List Nat := [1, 3, 1, 3, 1, 4, 3, 2, 2]
def baseStart_299365 : Nat := 118140960795 + 299365 * 2 ^ 59
def prefixEnd_299365 : Nat := 4983230072969 + 3 ^ 40 * 299365 * 2
def baseEnd_299365 : Nat := 136638343229623526009557

theorem tailTrace_299365 : CollatzResearch.WordTrace tailWord_299365 prefixEnd_299365 136638343229623526009557 := by
  unfold tailWord_299365
  simp only [CollatzResearch.WordTrace]
  refine ⟨10918738560459207316643549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7279159040306138211095699 10918738560459207316643549)
  ·
    refine ⟨4094526960172202743741331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10918738560459207316643549 4094526960172202743741331)
    ·
      refine ⟨6141790440258304115611997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4094526960172202743741331 6141790440258304115611997)
      ·
        refine ⟨2303171415096864043354499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6141790440258304115611997 2303171415096864043354499)
        ·
          refine ⟨3454757122645296065031749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2303171415096864043354499 3454757122645296065031749)
          ·
            refine ⟨647766960495993012193453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3454757122645296065031749 647766960495993012193453)
            ·
              refine ⟨242912610185997379572545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 647766960495993012193453 242912610185997379572545)
              ·
                refine ⟨182184457639498034679409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242912610185997379572545 182184457639498034679409)
                ·
                  refine ⟨136638343229623526009557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182184457639498034679409 136638343229623526009557)
                  ·
                    rfl

theorem cell20_299365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 2, 2].length) (baseStart_299365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299365 prefixEnd_299365 := by exact prefixLift 299365
  have htrace : WordTrace (prefixWord ++ tailWord_299365) baseStart_299365 baseEnd_299365 := by
    simpa [prefixWord, tailWord_299365, baseEnd_299365] using wordTrace_append hprefix tailTrace_299365
  have hstable : (prefixWord ++ tailWord_299365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299365).length < 2 ^ (prefixWord ++ tailWord_299365).sum := by decide
  have hdescent : baseEnd_299365 < baseStart_299365 := by decide
  rcases family_descends (prefixWord ++ tailWord_299365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299376 : List Nat := [2, 1, 1, 1, 4, 4, 2, 5]
def baseStart_299376 : Nat := 118140960795 + 299376 * 2 ^ 59
def prefixEnd_299376 : Nat := 4983230072969 + 3 ^ 40 * 299376 * 2
def baseEnd_299376 : Nat := 45547787976452125547615

theorem tailTrace_299376 : CollatzResearch.WordTrace tailWord_299376 prefixEnd_299376 45547787976452125547615 := by
  unfold tailWord_299376
  simp only [CollatzResearch.WordTrace]
  refine ⟨5459569881709678097646991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7279426508946237463529321 5459569881709678097646991)
  ·
    refine ⟨8189354822564517146470487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5459569881709678097646991 8189354822564517146470487)
    ·
      refine ⟨12284032233846775719705731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8189354822564517146470487 12284032233846775719705731)
      ·
        refine ⟨18426048350770163579558597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12284032233846775719705731 18426048350770163579558597)
        ·
          refine ⟨3454884065769405671167237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18426048350770163579558597 3454884065769405671167237)
          ·
            refine ⟨647790762331763563343857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3454884065769405671167237 647790762331763563343857)
            ·
              refine ⟨485843071748822672507893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 647790762331763563343857 485843071748822672507893)
              ·
                refine ⟨45547787976452125547615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 485843071748822672507893 45547787976452125547615)
                ·
                  rfl

theorem cell20_299376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 5].length) (baseStart_299376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299376 prefixEnd_299376 := by exact prefixLift 299376
  have htrace : WordTrace (prefixWord ++ tailWord_299376) baseStart_299376 baseEnd_299376 := by
    simpa [prefixWord, tailWord_299376, baseEnd_299376] using wordTrace_append hprefix tailTrace_299376
  have hstable : (prefixWord ++ tailWord_299376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299376).length < 2 ^ (prefixWord ++ tailWord_299376).sum := by decide
  have hdescent : baseEnd_299376 < baseStart_299376 := by decide
  rcases family_descends (prefixWord ++ tailWord_299376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299424 : List Nat := [2, 1, 1, 4, 1, 4, 1, 4, 2]
def baseStart_299424 : Nat := 118140960795 + 299424 * 2 ^ 59
def prefixEnd_299424 : Nat := 4983230072969 + 3 ^ 40 * 299424 * 2
def baseEnd_299424 : Nat := 136665272437281543042649

theorem tailTrace_299424 : CollatzResearch.WordTrace tailWord_299424 prefixEnd_299424 136665272437281543042649 := by
  unfold tailWord_299424
  simp only [CollatzResearch.WordTrace]
  refine ⟨5460445233622730196520663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7280593644830306928694217 5460445233622730196520663)
  ·
    refine ⟨8190667850434095294780995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5460445233622730196520663 8190667850434095294780995)
    ·
      refine ⟨12286001775651142942171493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8190667850434095294780995 12286001775651142942171493)
      ·
        refine ⟨2303625332934589301657155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12286001775651142942171493 2303625332934589301657155)
        ·
          refine ⟨3455437999401883952485733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2303625332934589301657155 3455437999401883952485733)
          ·
            refine ⟨647894624887853241091075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3455437999401883952485733 647894624887853241091075)
            ·
              refine ⟨971841937331779861636613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 647894624887853241091075 971841937331779861636613)
              ·
                refine ⟨182220363249708724056865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 971841937331779861636613 182220363249708724056865)
                ·
                  refine ⟨136665272437281543042649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182220363249708724056865 136665272437281543042649)
                  ·
                    rfl

theorem cell20_299424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 4, 2].length) (baseStart_299424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299424 prefixEnd_299424 := by exact prefixLift 299424
  have htrace : WordTrace (prefixWord ++ tailWord_299424) baseStart_299424 baseEnd_299424 := by
    simpa [prefixWord, tailWord_299424, baseEnd_299424] using wordTrace_append hprefix tailTrace_299424
  have hstable : (prefixWord ++ tailWord_299424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299424).length < 2 ^ (prefixWord ++ tailWord_299424).sum := by decide
  have hdescent : baseEnd_299424 < baseStart_299424 := by decide
  rcases family_descends (prefixWord ++ tailWord_299424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299431 : List Nat := [1, 1, 6, 1, 1, 4, 1, 5]
def baseStart_299431 : Nat := 118140960795 + 299431 * 2 ^ 59
def prefixEnd_299431 : Nat := 4983230072969 + 3 ^ 40 * 299431 * 2
def baseEnd_299431 : Nat := 45556155809340209936429

theorem tailTrace_299431 : CollatzResearch.WordTrace tailWord_299431 prefixEnd_299431 45556155809340209936429 := by
  unfold tailWord_299431
  simp only [CollatzResearch.WordTrace]
  refine ⟨10921145778220100588546147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7280763852146733725697431 10921145778220100588546147)
  ·
    refine ⟨16381718667330150882819221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10921145778220100588546147 16381718667330150882819221)
    ·
      refine ⟨767893062531100822632151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16381718667330150882819221 767893062531100822632151)
      ·
        refine ⟨1151839593796651233948227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 767893062531100822632151 1151839593796651233948227)
        ·
          refine ⟨1727759390694976850922341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1151839593796651233948227 1727759390694976850922341)
          ·
            refine ⟨323954885755308159547939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1727759390694976850922341 323954885755308159547939)
            ·
              refine ⟨485932328632962239321909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323954885755308159547939 485932328632962239321909)
              ·
                refine ⟨45556155809340209936429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 485932328632962239321909 45556155809340209936429)
                ·
                  rfl

theorem cell20_299431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 5].length) (baseStart_299431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299431 prefixEnd_299431 := by exact prefixLift 299431
  have htrace : WordTrace (prefixWord ++ tailWord_299431) baseStart_299431 baseEnd_299431 := by
    simpa [prefixWord, tailWord_299431, baseEnd_299431] using wordTrace_append hprefix tailTrace_299431
  have hstable : (prefixWord ++ tailWord_299431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299431).length < 2 ^ (prefixWord ++ tailWord_299431).sum := by decide
  have hdescent : baseEnd_299431 < baseStart_299431 := by decide
  rcases family_descends (prefixWord ++ tailWord_299431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299466 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 6]
def baseStart_299466 : Nat := 118140960795 + 299466 * 2 ^ 59
def prefixEnd_299466 : Nat := 4983230072969 + 3 ^ 40 * 299466 * 2
def baseEnd_299466 : Nat := 136684442381716063642477

theorem tailTrace_299466 : CollatzResearch.WordTrace tailWord_299466 prefixEnd_299466 136684442381716063642477 := by
  unfold tailWord_299466
  simp only [CollatzResearch.WordTrace]
  refine ⟨2730605583273325391517563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7281614888728867710713501 2730605583273325391517563)
  ·
    refine ⟨4095908374909988087276345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2730605583273325391517563 4095908374909988087276345)
    ·
      refine ⟨3071931281182491065457259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4095908374909988087276345 3071931281182491065457259)
      ·
        refine ⟨4607896921773736598185889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3071931281182491065457259 4607896921773736598185889)
        ·
          refine ⟨3455922691330302448639417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4607896921773736598185889 3455922691330302448639417)
          ·
            refine ⟨2591942018497726836479563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3455922691330302448639417 2591942018497726836479563)
            ·
              refine ⟨3887913027746590254719345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2591942018497726836479563 3887913027746590254719345)
              ·
                refine ⟨2915934770809942691039509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3887913027746590254719345 2915934770809942691039509)
                ·
                  refine ⟨136684442381716063642477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2915934770809942691039509 136684442381716063642477)
                  ·
                    rfl

theorem cell20_299466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_299466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299466 prefixEnd_299466 := by exact prefixLift 299466
  have htrace : WordTrace (prefixWord ++ tailWord_299466) baseStart_299466 baseEnd_299466 := by
    simpa [prefixWord, tailWord_299466, baseEnd_299466] using wordTrace_append hprefix tailTrace_299466
  have hstable : (prefixWord ++ tailWord_299466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299466).length < 2 ^ (prefixWord ++ tailWord_299466).sum := by decide
  have hdescent : baseEnd_299466 < baseStart_299466 := by decide
  rcases family_descends (prefixWord ++ tailWord_299466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299476 : List Nat := [2, 4, 1, 2, 2, 2, 1, 1, 5]
def baseStart_299476 : Nat := 118140960795 + 299476 * 2 ^ 59
def prefixEnd_299476 : Nat := 4983230072969 + 3 ^ 40 * 299476 * 2
def baseEnd_299476 : Nat := 136689006654200473309103

theorem tailTrace_299476 : CollatzResearch.WordTrace tailWord_299476 prefixEnd_299476 136689006654200473309103 := by
  unfold tailWord_299476
  simp only [CollatzResearch.WordTrace]
  refine ⟨5461393531528536636967141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7281858042038048849289521 5461393531528536636967141)
  ·
    refine ⟨1024011287161600619431339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5461393531528536636967141 1024011287161600619431339)
    ·
      refine ⟨1536016930742400929147009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1024011287161600619431339 1536016930742400929147009)
      ·
        refine ⟨1152012698056800696860257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1536016930742400929147009 1152012698056800696860257)
        ·
          refine ⟨864009523542600522645193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1152012698056800696860257 864009523542600522645193)
          ·
            refine ⟨648007142656950391983895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 864009523542600522645193 648007142656950391983895)
            ·
              refine ⟨972010713985425587975843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 648007142656950391983895 972010713985425587975843)
              ·
                refine ⟨1458016070978138381963765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 972010713985425587975843 1458016070978138381963765)
                ·
                  refine ⟨136689006654200473309103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1458016070978138381963765 136689006654200473309103)
                  ·
                    rfl

theorem cell20_299476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_299476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299476 prefixEnd_299476 := by exact prefixLift 299476
  have htrace : WordTrace (prefixWord ++ tailWord_299476) baseStart_299476 baseEnd_299476 := by
    simpa [prefixWord, tailWord_299476, baseEnd_299476] using wordTrace_append hprefix tailTrace_299476
  have hstable : (prefixWord ++ tailWord_299476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299476).length < 2 ^ (prefixWord ++ tailWord_299476).sum := by decide
  have hdescent : baseEnd_299476 < baseStart_299476 := by decide
  rcases family_descends (prefixWord ++ tailWord_299476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299504 : List Nat := [2, 1, 1, 1, 3, 3, 1, 4, 4]
def baseStart_299504 : Nat := 118140960795 + 299504 * 2 ^ 59
def prefixEnd_299504 : Nat := 4983230072969 + 3 ^ 40 * 299504 * 2
def baseEnd_299504 : Nat := 136701786617156820375655

theorem tailTrace_299504 : CollatzResearch.WordTrace tailWord_299504 prefixEnd_299504 136701786617156820375655 := by
  unfold tailWord_299504
  simp only [CollatzResearch.WordTrace]
  refine ⟨5461904153477817027976783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7282538871303756037302377 5461904153477817027976783)
  ·
    refine ⟨8192856230216725541965175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5461904153477817027976783 8192856230216725541965175)
    ·
      refine ⟨12289284345325088312947763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8192856230216725541965175 12289284345325088312947763)
      ·
        refine ⟨18433926517987632469421645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12289284345325088312947763 18433926517987632469421645)
        ·
          refine ⟨6912722444245362176033117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18433926517987632469421645 6912722444245362176033117)
          ·
            refine ⟨2592270916592010816012419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6912722444245362176033117 2592270916592010816012419)
            ·
              refine ⟨3888406374888016224018629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2592270916592010816012419 3888406374888016224018629)
              ·
                refine ⟨729076195291503042003493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3888406374888016224018629 729076195291503042003493)
                ·
                  refine ⟨136701786617156820375655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 729076195291503042003493 136701786617156820375655)
                  ·
                    rfl

theorem cell20_299504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_299504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299504 prefixEnd_299504 := by exact prefixLift 299504
  have htrace : WordTrace (prefixWord ++ tailWord_299504) baseStart_299504 baseEnd_299504 := by
    simpa [prefixWord, tailWord_299504, baseEnd_299504] using wordTrace_append hprefix tailTrace_299504
  have hstable : (prefixWord ++ tailWord_299504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299504).length < 2 ^ (prefixWord ++ tailWord_299504).sum := by decide
  have hdescent : baseEnd_299504 < baseStart_299504 := by decide
  rcases family_descends (prefixWord ++ tailWord_299504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299604 : List Nat := [2, 4, 1, 1, 1, 3, 3, 5]
def baseStart_299604 : Nat := 118140960795 + 299604 * 2 ^ 59
def prefixEnd_299604 : Nat := 4983230072969 + 3 ^ 40 * 299604 * 2
def baseEnd_299604 : Nat := 45582476447333639013971

theorem tailTrace_299604 : CollatzResearch.WordTrace tailWord_299604 prefixEnd_299604 45582476447333639013971 := by
  unfold tailWord_299604
  simp only [CollatzResearch.WordTrace]
  refine ⟨5463727803296675567296933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7284970404395567423062577 5463727803296675567296933)
  ·
    refine ⟨1024448963118126668868175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5463727803296675567296933 1024448963118126668868175)
    ·
      refine ⟨1536673444677190003302263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1024448963118126668868175 1536673444677190003302263)
      ·
        refine ⟨2305010167015785004953395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1536673444677190003302263 2305010167015785004953395)
        ·
          refine ⟨3457515250523677507430093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2305010167015785004953395 3457515250523677507430093)
          ·
            refine ⟨1296568218946379065286285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3457515250523677507430093 1296568218946379065286285)
            ·
              refine ⟨486213082104892149482357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1296568218946379065286285 486213082104892149482357)
              ·
                refine ⟨45582476447333639013971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 486213082104892149482357 45582476447333639013971)
                ·
                  rfl

theorem cell20_299604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 5].length) (baseStart_299604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299604 prefixEnd_299604 := by exact prefixLift 299604
  have htrace : WordTrace (prefixWord ++ tailWord_299604) baseStart_299604 baseEnd_299604 := by
    simpa [prefixWord, tailWord_299604, baseEnd_299604] using wordTrace_append hprefix tailTrace_299604
  have hstable : (prefixWord ++ tailWord_299604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299604).length < 2 ^ (prefixWord ++ tailWord_299604).sum := by decide
  have hdescent : baseEnd_299604 < baseStart_299604 := by decide
  rcases family_descends (prefixWord ++ tailWord_299604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299621 : List Nat := [1, 3, 1, 3, 4, 1, 3, 4]
def baseStart_299621 : Nat := 118140960795 + 299621 * 2 ^ 59
def prefixEnd_299621 : Nat := 4983230072969 + 3 ^ 40 * 299621 * 2
def baseEnd_299621 : Nat := 45585062868408137825059

theorem tailTrace_299621 : CollatzResearch.WordTrace tailWord_299621 prefixEnd_299621 45585062868408137825059 := by
  unfold tailWord_299621
  simp only [CollatzResearch.WordTrace]
  refine ⟨10928075647531763037962717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7285383765021175358641811 10928075647531763037962717)
  ·
    refine ⟨4098028367824411139236019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10928075647531763037962717 4098028367824411139236019)
    ·
      refine ⟨6147042551736616708854029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4098028367824411139236019 6147042551736616708854029)
      ·
        refine ⟨2305140956901231265820261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6147042551736616708854029 2305140956901231265820261)
        ·
          refine ⟨432213929418980862341299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2305140956901231265820261 432213929418980862341299)
          ·
            refine ⟨648320894128471293511949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432213929418980862341299 648320894128471293511949)
            ·
              refine ⟨243120335298176735066981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 648320894128471293511949 243120335298176735066981)
              ·
                refine ⟨45585062868408137825059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 243120335298176735066981 45585062868408137825059)
                ·
                  rfl

theorem cell20_299621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 4].length) (baseStart_299621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299621 prefixEnd_299621 := by exact prefixLift 299621
  have htrace : WordTrace (prefixWord ++ tailWord_299621) baseStart_299621 baseEnd_299621 := by
    simpa [prefixWord, tailWord_299621, baseEnd_299621] using wordTrace_append hprefix tailTrace_299621
  have hstable : (prefixWord ++ tailWord_299621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299621).length < 2 ^ (prefixWord ++ tailWord_299621).sum := by decide
  have hdescent : baseEnd_299621 < baseStart_299621 := by decide
  rcases family_descends (prefixWord ++ tailWord_299621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299645 : List Nat := [1, 4, 1, 1, 5, 2, 1, 2, 3]
def baseStart_299645 : Nat := 118140960795 + 299645 * 2 ^ 59
def prefixEnd_299645 : Nat := 4983230072969 + 3 ^ 40 * 299645 * 2
def baseEnd_299645 : Nat := 136766142859186996675079

theorem tailTrace_299645 : CollatzResearch.WordTrace tailWord_299645 prefixEnd_299645 136766142859186996675079 := by
  unfold tailWord_299645
  simp only [CollatzResearch.WordTrace]
  refine ⟨10928950999444815136836389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7285967332963210091224259 10928950999444815136836389)
  ·
    refine ⟨2049178312395902838156823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10928950999444815136836389 2049178312395902838156823)
    ·
      refine ⟨3073767468593854257235235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2049178312395902838156823 3073767468593854257235235)
      ·
        refine ⟨4610651202890781385852853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3073767468593854257235235 4610651202890781385852853)
        ·
          refine ⟨432248550271010754923705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4610651202890781385852853 432248550271010754923705)
          ·
            refine ⟨324186412703258066192779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 432248550271010754923705 324186412703258066192779)
            ·
              refine ⟨486279619054887099289169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324186412703258066192779 486279619054887099289169)
              ·
                refine ⟨364709714291165324466877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 486279619054887099289169 364709714291165324466877)
                ·
                  refine ⟨136766142859186996675079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 364709714291165324466877 136766142859186996675079)
                  ·
                    rfl

theorem cell20_299645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_299645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299645 prefixEnd_299645 := by exact prefixLift 299645
  have htrace : WordTrace (prefixWord ++ tailWord_299645) baseStart_299645 baseEnd_299645 := by
    simpa [prefixWord, tailWord_299645, baseEnd_299645] using wordTrace_append hprefix tailTrace_299645
  have hstable : (prefixWord ++ tailWord_299645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299645).length < 2 ^ (prefixWord ++ tailWord_299645).sum := by decide
  have hdescent : baseEnd_299645 < baseStart_299645 := by decide
  rcases family_descends (prefixWord ++ tailWord_299645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299649 : List Nat := [1, 2, 4, 2, 1, 1, 3, 1, 5]
def baseStart_299649 : Nat := 118140960795 + 299649 * 2 ^ 59
def prefixEnd_299649 : Nat := 4983230072969 + 3 ^ 40 * 299649 * 2
def baseEnd_299649 : Nat := 136767968568180760541729

theorem tailTrace_299649 : CollatzResearch.WordTrace tailWord_299649 prefixEnd_299649 136767968568180760541729 := by
  unfold tailWord_299649
  simp only [CollatzResearch.WordTrace]
  refine ⟨10929096891430323819982001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7286064594286882546654667 10929096891430323819982001)
  ·
    refine ⟨8196822668572742864986501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10929096891430323819982001 8196822668572742864986501)
    ·
      refine ⟨1536904250357389287184969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8196822668572742864986501 1536904250357389287184969)
      ·
        refine ⟨1152678187768041965388727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1536904250357389287184969 1152678187768041965388727)
        ·
          refine ⟨1729017281652062948083091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1152678187768041965388727 1729017281652062948083091)
          ·
            refine ⟨2593525922478094422124637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1729017281652062948083091 2593525922478094422124637)
            ·
              refine ⟨972572220929285408296739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2593525922478094422124637 972572220929285408296739)
              ·
                refine ⟨1458858331393928112445109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 972572220929285408296739 1458858331393928112445109)
                ·
                  refine ⟨136767968568180760541729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1458858331393928112445109 136767968568180760541729)
                  ·
                    rfl

theorem cell20_299649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_299649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299649 prefixEnd_299649 := by exact prefixLift 299649
  have htrace : WordTrace (prefixWord ++ tailWord_299649) baseStart_299649 baseEnd_299649 := by
    simpa [prefixWord, tailWord_299649, baseEnd_299649] using wordTrace_append hprefix tailTrace_299649
  have hstable : (prefixWord ++ tailWord_299649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299649).length < 2 ^ (prefixWord ++ tailWord_299649).sum := by decide
  have hdescent : baseEnd_299649 < baseStart_299649 := by decide
  rcases family_descends (prefixWord ++ tailWord_299649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299652 : List Nat := [2, 3, 2, 1, 3, 1, 2, 4, 2]
def baseStart_299652 : Nat := 118140960795 + 299652 * 2 ^ 59
def prefixEnd_299652 : Nat := 4983230072969 + 3 ^ 40 * 299652 * 2
def baseEnd_299652 : Nat := 136769337849926083441717

theorem tailTrace_299652 : CollatzResearch.WordTrace tailWord_299652 prefixEnd_299652 136769337849926083441717 := by
  unfold tailWord_299652
  simp only [CollatzResearch.WordTrace]
  refine ⟨5464603155209727666170605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7286137540279636888227473 5464603155209727666170605)
  ·
    refine ⟨2049226183203647874813977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5464603155209727666170605 2049226183203647874813977)
    ·
      refine ⟨1536919637402735906110483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2049226183203647874813977 1536919637402735906110483)
      ·
        refine ⟨2305379456104103859165725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1536919637402735906110483 2305379456104103859165725)
        ·
          refine ⟨864517296039038947187147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2305379456104103859165725 864517296039038947187147)
          ·
            refine ⟨1296775944058558420780721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 864517296039038947187147 1296775944058558420780721)
            ·
              refine ⟨972581958043918815585541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1296775944058558420780721 972581958043918815585541)
              ·
                refine ⟨182359117133234777922289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 972581958043918815585541 182359117133234777922289)
                ·
                  refine ⟨136769337849926083441717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182359117133234777922289 136769337849926083441717)
                  ·
                    rfl

theorem cell20_299652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_299652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299652 prefixEnd_299652 := by exact prefixLift 299652
  have htrace : WordTrace (prefixWord ++ tailWord_299652) baseStart_299652 baseEnd_299652 := by
    simpa [prefixWord, tailWord_299652, baseEnd_299652] using wordTrace_append hprefix tailTrace_299652
  have hstable : (prefixWord ++ tailWord_299652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299652).length < 2 ^ (prefixWord ++ tailWord_299652).sum := by decide
  have hdescent : baseEnd_299652 < baseStart_299652 := by decide
  rcases family_descends (prefixWord ++ tailWord_299652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299680 : List Nat := [2, 1, 1, 4, 4, 1, 1, 6]
def baseStart_299680 : Nat := 118140960795 + 299680 * 2 ^ 59
def prefixEnd_299680 : Nat := 4983230072969 + 3 ^ 40 * 299680 * 2
def baseEnd_299680 : Nat := 45594039270960810169423

theorem tailTrace_299680 : CollatzResearch.WordTrace tailWord_299680 prefixEnd_299680 45594039270960810169423 := by
  unfold tailWord_299680
  simp only [CollatzResearch.WordTrace]
  refine ⟨5465113777159008057180247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7286818369545344076240329 5465113777159008057180247)
  ·
    refine ⟨8197670665738512085770371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5465113777159008057180247 8197670665738512085770371)
    ·
      refine ⟨12296505998607768128655557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8197670665738512085770371 12296505998607768128655557)
      ·
        refine ⟨2305594874738956524122917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12296505998607768128655557 2305594874738956524122917)
        ·
          refine ⟨432299039013554348273047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2305594874738956524122917 432299039013554348273047)
          ·
            refine ⟨648448558520331522409571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432299039013554348273047 648448558520331522409571)
            ·
              refine ⟨972672837780497283614357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 648448558520331522409571 972672837780497283614357)
              ·
                refine ⟨45594039270960810169423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 972672837780497283614357 45594039270960810169423)
                ·
                  rfl

theorem cell20_299680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 6].length) (baseStart_299680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299680 prefixEnd_299680 := by exact prefixLift 299680
  have htrace : WordTrace (prefixWord ++ tailWord_299680) baseStart_299680 baseEnd_299680 := by
    simpa [prefixWord, tailWord_299680, baseEnd_299680] using wordTrace_append hprefix tailTrace_299680
  have hstable : (prefixWord ++ tailWord_299680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299680).length < 2 ^ (prefixWord ++ tailWord_299680).sum := by decide
  have hdescent : baseEnd_299680 < baseStart_299680 := by decide
  rcases family_descends (prefixWord ++ tailWord_299680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299697 : List Nat := [1, 2, 2, 6, 1, 2, 6]
def baseStart_299697 : Nat := 118140960795 + 299697 * 2 ^ 59
def prefixEnd_299697 : Nat := 4983230072969 + 3 ^ 40 * 299697 * 2
def baseEnd_299697 : Nat := 15198875230678436326837

theorem tailTrace_299697 : CollatzResearch.WordTrace tailWord_299697 prefixEnd_299697 15198875230678436326837 := by
  unfold tailWord_299697
  simp only [CollatzResearch.WordTrace]
  refine ⟨10930847595256428017729345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7287231730170952011819563 10930847595256428017729345)
  ·
    refine ⟨8198135696442321013297009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10930847595256428017729345 8198135696442321013297009)
    ·
      refine ⟨6148601772331740759972757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8198135696442321013297009 6148601772331740759972757)
      ·
        refine ⟨288215708078050348123723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6148601772331740759972757 288215708078050348123723)
        ·
          refine ⟨432323562117075522185585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288215708078050348123723 432323562117075522185585)
          ·
            refine ⟨324242671587806641639189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 432323562117075522185585 324242671587806641639189)
            ·
              refine ⟨15198875230678436326837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 324242671587806641639189 15198875230678436326837)
              ·
                rfl

theorem cell20_299697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 6].length) (baseStart_299697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299697 prefixEnd_299697 := by exact prefixLift 299697
  have htrace : WordTrace (prefixWord ++ tailWord_299697) baseStart_299697 baseEnd_299697 := by
    simpa [prefixWord, tailWord_299697, baseEnd_299697] using wordTrace_append hprefix tailTrace_299697
  have hstable : (prefixWord ++ tailWord_299697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299697).length < 2 ^ (prefixWord ++ tailWord_299697).sum := by decide
  have hdescent : baseEnd_299697 < baseStart_299697 := by decide
  rcases family_descends (prefixWord ++ tailWord_299697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299711 : List Nat := [1, 1, 2, 2, 2, 6, 1, 1, 4]
def baseStart_299711 : Nat := 118140960795 + 299711 * 2 ^ 59
def prefixEnd_299711 : Nat := 4983230072969 + 3 ^ 40 * 299711 * 2
def baseEnd_299711 : Nat := 136796267057584100474809

theorem tailTrace_299711 : CollatzResearch.WordTrace tailWord_299711 prefixEnd_299711 136796267057584100474809 := by
  unfold tailWord_299711
  simp only [CollatzResearch.WordTrace]
  refine ⟨10931358217205708408738987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7287572144803805605825991 10931358217205708408738987)
  ·
    refine ⟨16397037325808562613108481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10931358217205708408738987 16397037325808562613108481)
    ·
      refine ⟨12297777994356421959831361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16397037325808562613108481 12297777994356421959831361)
      ·
        refine ⟨9223333495767316469873521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12297777994356421959831361 9223333495767316469873521)
        ·
          refine ⟨6917500121825487352405141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9223333495767316469873521 6917500121825487352405141)
          ·
            refine ⟨324257818210569719643991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6917500121825487352405141 324257818210569719643991)
            ·
              refine ⟨486386727315854579465987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324257818210569719643991 486386727315854579465987)
              ·
                refine ⟨729580090973781869198981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 486386727315854579465987 729580090973781869198981)
                ·
                  refine ⟨136796267057584100474809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 729580090973781869198981 136796267057584100474809)
                  ·
                    rfl

theorem cell20_299711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 4].length) (baseStart_299711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299711 prefixEnd_299711 := by exact prefixLift 299711
  have htrace : WordTrace (prefixWord ++ tailWord_299711) baseStart_299711 baseEnd_299711 := by
    simpa [prefixWord, tailWord_299711, baseEnd_299711] using wordTrace_append hprefix tailTrace_299711
  have hstable : (prefixWord ++ tailWord_299711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299711).length < 2 ^ (prefixWord ++ tailWord_299711).sum := by decide
  have hdescent : baseEnd_299711 < baseStart_299711 := by decide
  rcases family_descends (prefixWord ++ tailWord_299711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299766 : List Nat := [5, 1, 1, 1, 1, 2, 3, 4, 2]
def baseStart_299766 : Nat := 118140960795 + 299766 * 2 ^ 59
def prefixEnd_299766 : Nat := 4983230072969 + 3 ^ 40 * 299766 * 2
def baseEnd_299766 : Nat := 136821370556248353641251

theorem tailTrace_299766 : CollatzResearch.WordTrace tailWord_299766 prefixEnd_299766 136821370556248353641251 := by
  unfold tailWord_299766
  simp only [CollatzResearch.WordTrace]
  refine ⟨683335264500403300124447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7288909488004301867994101 683335264500403300124447)
  ·
    refine ⟨1025002896750604950186671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 683335264500403300124447 1025002896750604950186671)
    ·
      refine ⟨1537504345125907425280007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1025002896750604950186671 1537504345125907425280007)
      ·
        refine ⟨2306256517688861137920011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1537504345125907425280007 2306256517688861137920011)
        ·
          refine ⟨3459384776533291706880017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2306256517688861137920011 3459384776533291706880017)
          ·
            refine ⟨2594538582399968780160013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3459384776533291706880017 2594538582399968780160013)
            ·
              refine ⟨972951968399988292560005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2594538582399968780160013 972951968399988292560005)
              ·
                refine ⟨182428494074997804855001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 972951968399988292560005 182428494074997804855001)
                ·
                  refine ⟨136821370556248353641251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182428494074997804855001 136821370556248353641251)
                  ·
                    rfl

theorem cell20_299766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_299766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299766 prefixEnd_299766 := by exact prefixLift 299766
  have htrace : WordTrace (prefixWord ++ tailWord_299766) baseStart_299766 baseEnd_299766 := by
    simpa [prefixWord, tailWord_299766, baseEnd_299766] using wordTrace_append hprefix tailTrace_299766
  have hstable : (prefixWord ++ tailWord_299766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299766).length < 2 ^ (prefixWord ++ tailWord_299766).sum := by decide
  have hdescent : baseEnd_299766 < baseStart_299766 := by decide
  rcases family_descends (prefixWord ++ tailWord_299766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299804 : List Nat := [2, 2, 3, 1, 1, 4, 2, 3, 2]
def baseStart_299804 : Nat := 118140960795 + 299804 * 2 ^ 59
def prefixEnd_299804 : Nat := 4983230072969 + 3 ^ 40 * 299804 * 2
def baseEnd_299804 : Nat := 136838714791689110374429

theorem tailTrace_299804 : CollatzResearch.WordTrace tailWord_299804 prefixEnd_299804 136838714791689110374429 := by
  unfold tailWord_299804
  simp only [CollatzResearch.WordTrace]
  refine ⟨5467375102934392645937233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7289833470579190194582977 5467375102934392645937233)
  ·
    refine ⟨4100531327200794484452925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5467375102934392645937233 4100531327200794484452925)
    ·
      refine ⟨1537699247700297931669847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4100531327200794484452925 1537699247700297931669847)
      ·
        refine ⟨2306548871550446897504771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1537699247700297931669847 2306548871550446897504771)
        ·
          refine ⟨3459823307325670346257157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2306548871550446897504771 3459823307325670346257157)
          ·
            refine ⟨648716870123563189923217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3459823307325670346257157 648716870123563189923217)
            ·
              refine ⟨486537652592672392442413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 648716870123563189923217 486537652592672392442413)
              ·
                refine ⟨182451619722252147165905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 486537652592672392442413 182451619722252147165905)
                ·
                  refine ⟨136838714791689110374429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182451619722252147165905 136838714791689110374429)
                  ·
                    rfl

theorem cell20_299804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 3, 2].length) (baseStart_299804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299804 prefixEnd_299804 := by exact prefixLift 299804
  have htrace : WordTrace (prefixWord ++ tailWord_299804) baseStart_299804 baseEnd_299804 := by
    simpa [prefixWord, tailWord_299804, baseEnd_299804] using wordTrace_append hprefix tailTrace_299804
  have hstable : (prefixWord ++ tailWord_299804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299804).length < 2 ^ (prefixWord ++ tailWord_299804).sum := by decide
  have hdescent : baseEnd_299804 < baseStart_299804 := by decide
  rcases family_descends (prefixWord ++ tailWord_299804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299821 : List Nat := [1, 5, 3, 2, 1, 1, 2, 1, 4]
def baseStart_299821 : Nat := 118140960795 + 299821 * 2 ^ 59
def prefixEnd_299821 : Nat := 4983230072969 + 3 ^ 40 * 299821 * 2
def baseEnd_299821 : Nat := 136846474054912606807693

theorem tailTrace_299821 : CollatzResearch.WordTrace tailWord_299821 prefixEnd_299821 136846474054912606807693 := by
  unfold tailWord_299821
  simp only [CollatzResearch.WordTrace]
  refine ⟨10935370246807197195243317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7290246831204798130162211 10935370246807197195243317)
  ·
    refine ⟨1025190960638174737054061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10935370246807197195243317 1025190960638174737054061)
    ·
      refine ⟨384446610239315526395273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1025190960638174737054061 384446610239315526395273)
      ·
        refine ⟨288334957679486644796455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 384446610239315526395273 288334957679486644796455)
        ·
          refine ⟨432502436519229967194683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288334957679486644796455 432502436519229967194683)
          ·
            refine ⟨648753654778844950792025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432502436519229967194683 648753654778844950792025)
            ·
              refine ⟨486565241084133713094019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 648753654778844950792025 486565241084133713094019)
              ·
                refine ⟨729847861626200569641029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 486565241084133713094019 729847861626200569641029)
                ·
                  refine ⟨136846474054912606807693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 729847861626200569641029 136846474054912606807693)
                  ·
                    rfl

theorem cell20_299821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_299821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299821 prefixEnd_299821 := by exact prefixLift 299821
  have htrace : WordTrace (prefixWord ++ tailWord_299821) baseStart_299821 baseEnd_299821 := by
    simpa [prefixWord, tailWord_299821, baseEnd_299821] using wordTrace_append hprefix tailTrace_299821
  have hstable : (prefixWord ++ tailWord_299821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299821).length < 2 ^ (prefixWord ++ tailWord_299821).sum := by decide
  have hdescent : baseEnd_299821 < baseStart_299821 := by decide
  rcases family_descends (prefixWord ++ tailWord_299821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299825 : List Nat := [1, 2, 2, 3, 2, 1, 1, 6, 2]
def baseStart_299825 : Nat := 118140960795 + 299825 * 2 ^ 59
def prefixEnd_299825 : Nat := 4983230072969 + 3 ^ 40 * 299825 * 2
def baseEnd_299825 : Nat := 136848299763906370674343

theorem tailTrace_299825 : CollatzResearch.WordTrace tailWord_299825 prefixEnd_299825 136848299763906370674343 := by
  unfold tailWord_299825
  simp only [CollatzResearch.WordTrace]
  refine ⟨10935516138792705878388929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7290344092528470585592619 10935516138792705878388929)
  ·
    refine ⟨8201637104094529408791697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10935516138792705878388929 8201637104094529408791697)
    ·
      refine ⟨6151227828070897056593773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8201637104094529408791697 6151227828070897056593773)
      ·
        refine ⟨2306710435526586396222665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6151227828070897056593773 2306710435526586396222665)
        ·
          refine ⟨1730032826644939797166999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2306710435526586396222665 1730032826644939797166999)
          ·
            refine ⟨2595049239967409695750499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1730032826644939797166999 2595049239967409695750499)
            ·
              refine ⟨3892573859951114543625749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2595049239967409695750499 3892573859951114543625749)
              ·
                refine ⟨182464399685208494232457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3892573859951114543625749 182464399685208494232457)
                ·
                  refine ⟨136848299763906370674343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182464399685208494232457 136848299763906370674343)
                  ·
                    rfl

theorem cell20_299825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 6, 2].length) (baseStart_299825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299825 prefixEnd_299825 := by exact prefixLift 299825
  have htrace : WordTrace (prefixWord ++ tailWord_299825) baseStart_299825 baseEnd_299825 := by
    simpa [prefixWord, tailWord_299825, baseEnd_299825] using wordTrace_append hprefix tailTrace_299825
  have hstable : (prefixWord ++ tailWord_299825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299825).length < 2 ^ (prefixWord ++ tailWord_299825).sum := by decide
  have hdescent : baseEnd_299825 < baseStart_299825 := by decide
  rcases family_descends (prefixWord ++ tailWord_299825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299935 : List Nat := [1, 1, 2, 5, 2, 3, 2, 2, 2]
def baseStart_299935 : Nat := 118140960795 + 299935 * 2 ^ 59
def prefixEnd_299935 : Nat := 4983230072969 + 3 ^ 40 * 299935 * 2
def baseEnd_299935 : Nat := 136898506761234877007227

theorem tailTrace_299935 : CollatzResearch.WordTrace tailWord_299935 prefixEnd_299935 136898506761234877007227 := by
  unfold tailWord_299935
  simp only [CollatzResearch.WordTrace]
  refine ⟨10939528168394194664893259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7293018778929463109928839 10939528168394194664893259)
  ·
    refine ⟨16409292252591291997339889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10939528168394194664893259 16409292252591291997339889)
    ·
      refine ⟨12306969189443468998004917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16409292252591291997339889 12306969189443468998004917)
      ·
        refine ⟨1153778361510325218562961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12306969189443468998004917 1153778361510325218562961)
        ·
          refine ⟨865333771132743913922221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1153778361510325218562961 865333771132743913922221)
          ·
            refine ⟨324500164174778967720833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 865333771132743913922221 324500164174778967720833)
            ·
              refine ⟨243375123131084225790625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 324500164174778967720833 243375123131084225790625)
              ·
                refine ⟨182531342348313169342969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 243375123131084225790625 182531342348313169342969)
                ·
                  refine ⟨136898506761234877007227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182531342348313169342969 136898506761234877007227)
                  ·
                    rfl

theorem cell20_299935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 2, 2].length) (baseStart_299935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299935 prefixEnd_299935 := by exact prefixLift 299935
  have htrace : WordTrace (prefixWord ++ tailWord_299935) baseStart_299935 baseEnd_299935 := by
    simpa [prefixWord, tailWord_299935, baseEnd_299935] using wordTrace_append hprefix tailTrace_299935
  have hstable : (prefixWord ++ tailWord_299935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299935).length < 2 ^ (prefixWord ++ tailWord_299935).sum := by decide
  have hdescent : baseEnd_299935 < baseStart_299935 := by decide
  rcases family_descends (prefixWord ++ tailWord_299935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299936 : List Nat := [2, 1, 1, 4, 1, 1, 2, 3, 5]
def baseStart_299936 : Nat := 118140960795 + 299936 * 2 ^ 59
def prefixEnd_299936 : Nat := 4983230072969 + 3 ^ 40 * 299936 * 2
def baseEnd_299936 : Nat := 136898963188483317973889

theorem tailTrace_299936 : CollatzResearch.WordTrace tailWord_299936 prefixEnd_299936 136898963188483317973889 := by
  unfold tailWord_299936
  simp only [CollatzResearch.WordTrace]
  refine ⟨5469782320695285917839831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7293043094260381223786441 5469782320695285917839831)
  ·
    refine ⟨8204673481042928876759747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5469782320695285917839831 8204673481042928876759747)
    ·
      refine ⟨12307010221564393315139621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8204673481042928876759747 12307010221564393315139621)
      ·
        refine ⟨2307564416543323746588679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12307010221564393315139621 2307564416543323746588679)
        ·
          refine ⟨3461346624814985619883019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2307564416543323746588679 3461346624814985619883019)
          ·
            refine ⟨5192019937222478429824529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3461346624814985619883019 5192019937222478429824529)
            ·
              refine ⟨3894014952916858822368397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5192019937222478429824529 3894014952916858822368397)
              ·
                refine ⟨1460255607343822058388149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3894014952916858822368397 1460255607343822058388149)
                ·
                  refine ⟨136898963188483317973889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1460255607343822058388149 136898963188483317973889)
                  ·
                    rfl

theorem cell20_299936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_299936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299936 prefixEnd_299936 := by exact prefixLift 299936
  have htrace : WordTrace (prefixWord ++ tailWord_299936) baseStart_299936 baseEnd_299936 := by
    simpa [prefixWord, tailWord_299936, baseEnd_299936] using wordTrace_append hprefix tailTrace_299936
  have hstable : (prefixWord ++ tailWord_299936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299936).length < 2 ^ (prefixWord ++ tailWord_299936).sum := by decide
  have hdescent : baseEnd_299936 < baseStart_299936 := by decide
  rcases family_descends (prefixWord ++ tailWord_299936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299956 : List Nat := [2, 5, 2, 1, 1, 2, 1, 2, 4]
def baseStart_299956 : Nat := 118140960795 + 299956 * 2 ^ 59
def prefixEnd_299956 : Nat := 4983230072969 + 3 ^ 40 * 299956 * 2
def baseEnd_299956 : Nat := 136908091733452137307141

theorem tailTrace_299956 : CollatzResearch.WordTrace tailWord_299956 prefixEnd_299956 136908091733452137307141 := by
  unfold tailWord_299956
  simp only [CollatzResearch.WordTrace]
  refine ⟨5470147050659057625703861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7293529400878743500938481 5470147050659057625703861)
  ·
    refine ⟨512826285999286652409737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5470147050659057625703861 512826285999286652409737)
    ·
      refine ⟨384619714499464989307303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 512826285999286652409737 384619714499464989307303)
      ·
        refine ⟨576929571749197483960955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384619714499464989307303 576929571749197483960955)
        ·
          refine ⟨865394357623796225941433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 576929571749197483960955 865394357623796225941433)
          ·
            refine ⟨649045768217847169456075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 865394357623796225941433 649045768217847169456075)
            ·
              refine ⟨973568652326770754184113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 649045768217847169456075 973568652326770754184113)
              ·
                refine ⟨730176489245078065638085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 973568652326770754184113 730176489245078065638085)
                ·
                  refine ⟨136908091733452137307141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 730176489245078065638085 136908091733452137307141)
                  ·
                    rfl

theorem cell20_299956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_299956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299956 prefixEnd_299956 := by exact prefixLift 299956
  have htrace : WordTrace (prefixWord ++ tailWord_299956) baseStart_299956 baseEnd_299956 := by
    simpa [prefixWord, tailWord_299956, baseEnd_299956] using wordTrace_append hprefix tailTrace_299956
  have hstable : (prefixWord ++ tailWord_299956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299956).length < 2 ^ (prefixWord ++ tailWord_299956).sum := by decide
  have hdescent : baseEnd_299956 < baseStart_299956 := by decide
  rcases family_descends (prefixWord ++ tailWord_299956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299960 : List Nat := [2, 1, 2, 1, 2, 5, 1, 2, 4]
def baseStart_299960 : Nat := 118140960795 + 299960 * 2 ^ 59
def prefixEnd_299960 : Nat := 4983230072969 + 3 ^ 40 * 299960 * 2
def baseEnd_299960 : Nat := 136909917442445901173791

theorem tailTrace_299960 : CollatzResearch.WordTrace tailWord_299960 prefixEnd_299960 136909917442445901173791 := by
  unfold tailWord_299960
  simp only [CollatzResearch.WordTrace]
  refine ⟨5470219996651811967276667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7293626662202415956368889 5470219996651811967276667)
  ·
    refine ⟨8205329994977717950915001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5470219996651811967276667 8205329994977717950915001)
    ·
      refine ⟨6153997496233288463186251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8205329994977717950915001 6153997496233288463186251)
      ·
        refine ⟨9230996244349932694779377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6153997496233288463186251 9230996244349932694779377)
        ·
          refine ⟨6923247183262449521084533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9230996244349932694779377 6923247183262449521084533)
          ·
            refine ⟨649054423430854642601675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6923247183262449521084533 649054423430854642601675)
            ·
              refine ⟨973581635146281963902513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 649054423430854642601675 973581635146281963902513)
              ·
                refine ⟨730186226359711472926885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 973581635146281963902513 730186226359711472926885)
                ·
                  refine ⟨136909917442445901173791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 730186226359711472926885 136909917442445901173791)
                  ·
                    rfl

theorem cell20_299960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_299960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_299960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_299960 prefixEnd_299960 := by exact prefixLift 299960
  have htrace : WordTrace (prefixWord ++ tailWord_299960) baseStart_299960 baseEnd_299960 := by
    simpa [prefixWord, tailWord_299960, baseEnd_299960] using wordTrace_append hprefix tailTrace_299960
  have hstable : (prefixWord ++ tailWord_299960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299960).length < 2 ^ (prefixWord ++ tailWord_299960).sum := by decide
  have hdescent : baseEnd_299960 < baseStart_299960 := by decide
  rcases family_descends (prefixWord ++ tailWord_299960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300018 : List Nat := [3, 2, 1, 5, 1, 2, 2, 4]
def baseStart_300018 : Nat := 118140960795 + 300018 * 2 ^ 59
def prefixEnd_300018 : Nat := 4983230072969 + 3 ^ 40 * 300018 * 2
def baseEnd_300018 : Nat := 45645463407618492413407

theorem tailTrace_300018 : CollatzResearch.WordTrace tailWord_300018 prefixEnd_300018 45645463407618492413407 := by
  unfold tailWord_300018
  simp only [CollatzResearch.WordTrace]
  refine ⟨2735638856773374960041177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7295036951395666560109805 2735638856773374960041177)
  ·
    refine ⟨2051729142580031220030883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2735638856773374960041177 2051729142580031220030883)
    ·
      refine ⟨3077593713870046830046325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2051729142580031220030883 3077593713870046830046325)
      ·
        refine ⟨288524410675316890316843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3077593713870046830046325 288524410675316890316843)
        ·
          refine ⟨432786616012975335475265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288524410675316890316843 432786616012975335475265)
          ·
            refine ⟨324589962009731501606449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 432786616012975335475265 324589962009731501606449)
            ·
              refine ⟨243442471507298626204837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 324589962009731501606449 243442471507298626204837)
              ·
                refine ⟨45645463407618492413407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 243442471507298626204837 45645463407618492413407)
                ·
                  rfl

theorem cell20_300018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_300018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300018 prefixEnd_300018 := by exact prefixLift 300018
  have htrace : WordTrace (prefixWord ++ tailWord_300018) baseStart_300018 baseEnd_300018 := by
    simpa [prefixWord, tailWord_300018, baseEnd_300018] using wordTrace_append hprefix tailTrace_300018
  have hstable : (prefixWord ++ tailWord_300018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300018).length < 2 ^ (prefixWord ++ tailWord_300018).sum := by decide
  have hdescent : baseEnd_300018 < baseStart_300018 := by decide
  rcases family_descends (prefixWord ++ tailWord_300018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300022 : List Nat := [5, 1, 1, 1, 3, 2, 1, 6]
def baseStart_300022 : Nat := 118140960795 + 300022 * 2 ^ 59
def prefixEnd_300022 : Nat := 4983230072969 + 3 ^ 40 * 300022 * 2
def baseEnd_300022 : Nat := 45646071977283080368957

theorem tailTrace_300022 : CollatzResearch.WordTrace tailWord_300022 prefixEnd_300022 45646071977283080368957 := by
  unfold tailWord_300022
  simp only [CollatzResearch.WordTrace]
  refine ⟨683918832442438032706895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7295134212719339015540213 683918832442438032706895)
  ·
    refine ⟨1025878248663657049060343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 683918832442438032706895 1025878248663657049060343)
    ·
      refine ⟨1538817372995485573590515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1025878248663657049060343 1538817372995485573590515)
      ·
        refine ⟨2308226059493228360385773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1538817372995485573590515 2308226059493228360385773)
        ·
          refine ⟨865584772309960635144665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2308226059493228360385773 865584772309960635144665)
          ·
            refine ⟨649188579232470476358499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 865584772309960635144665 649188579232470476358499)
            ·
              refine ⟨973782868848705714537749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 649188579232470476358499 973782868848705714537749)
              ·
                refine ⟨45646071977283080368957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 973782868848705714537749 45646071977283080368957)
                ·
                  rfl

theorem cell20_300022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_300022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300022 prefixEnd_300022 := by exact prefixLift 300022
  have htrace : WordTrace (prefixWord ++ tailWord_300022) baseStart_300022 baseEnd_300022 := by
    simpa [prefixWord, tailWord_300022, baseEnd_300022] using wordTrace_append hprefix tailTrace_300022
  have hstable : (prefixWord ++ tailWord_300022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300022).length < 2 ^ (prefixWord ++ tailWord_300022).sum := by decide
  have hdescent : baseEnd_300022 < baseStart_300022 := by decide
  rcases family_descends (prefixWord ++ tailWord_300022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300043 : List Nat := [1, 1, 1, 1, 6, 4, 6]
def baseStart_300043 : Nat := 118140960795 + 300043 * 2 ^ 59
def prefixEnd_300043 : Nat := 4983230072969 + 3 ^ 40 * 300043 * 2
def baseEnd_300043 : Nat := 15216422322674055711865

theorem tailTrace_300043 : CollatzResearch.WordTrace tailWord_300043 prefixEnd_300043 15216422322674055711865 := by
  unfold tailWord_300043
  simp only [CollatzResearch.WordTrace]
  refine ⟨10943467252002929109824783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7295644834668619406549855 10943467252002929109824783)
  ·
    refine ⟨16415200878004393664737175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10943467252002929109824783 16415200878004393664737175)
    ·
      refine ⟨24622801317006590497105763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16415200878004393664737175 24622801317006590497105763)
      ·
        refine ⟨36934201975509885745658645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24622801317006590497105763 36934201975509885745658645)
        ·
          refine ⟨1731290717602025894327749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36934201975509885745658645 1731290717602025894327749)
          ·
            refine ⟨324617009550379855186453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1731290717602025894327749 324617009550379855186453)
            ·
              refine ⟨15216422322674055711865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 324617009550379855186453 15216422322674055711865)
              ·
                rfl

theorem cell20_300043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 6].length) (baseStart_300043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300043 prefixEnd_300043 := by exact prefixLift 300043
  have htrace : WordTrace (prefixWord ++ tailWord_300043) baseStart_300043 baseEnd_300043 := by
    simpa [prefixWord, tailWord_300043, baseEnd_300043] using wordTrace_append hprefix tailTrace_300043
  have hstable : (prefixWord ++ tailWord_300043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300043).length < 2 ^ (prefixWord ++ tailWord_300043).sum := by decide
  have hdescent : baseEnd_300043 < baseStart_300043 := by decide
  rcases family_descends (prefixWord ++ tailWord_300043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300053 : List Nat := [1, 3, 2, 1, 4, 3, 1, 1, 4]
def baseStart_300053 : Nat := 118140960795 + 300053 * 2 ^ 59
def prefixEnd_300053 : Nat := 4983230072969 + 3 ^ 40 * 300053 * 2
def baseEnd_300053 : Nat := 136952365176550911073411

theorem tailTrace_300053 : CollatzResearch.WordTrace tailWord_300053 prefixEnd_300053 136952365176550911073411 := by
  unfold tailWord_300053
  simp only [CollatzResearch.WordTrace]
  refine ⟨10943831981966700817688813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7295887987977800545125875 10943831981966700817688813)
  ·
    refine ⟨4103936993237512806633305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10943831981966700817688813 4103936993237512806633305)
    ·
      refine ⟨3077952744928134604974979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4103936993237512806633305 3077952744928134604974979)
      ·
        refine ⟨4616929117392201907462469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3077952744928134604974979 4616929117392201907462469)
        ·
          refine ⟨865674209511037857649213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4616929117392201907462469 865674209511037857649213)
          ·
            refine ⟨324627828566639196618455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 865674209511037857649213 324627828566639196618455)
            ·
              refine ⟨486941742849958794927683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324627828566639196618455 486941742849958794927683)
              ·
                refine ⟨730412614274938192391525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 486941742849958794927683 730412614274938192391525)
                ·
                  refine ⟨136952365176550911073411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 730412614274938192391525 136952365176550911073411)
                  ·
                    rfl

theorem cell20_300053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_300053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300053 prefixEnd_300053 := by exact prefixLift 300053
  have htrace : WordTrace (prefixWord ++ tailWord_300053) baseStart_300053 baseEnd_300053 := by
    simpa [prefixWord, tailWord_300053, baseEnd_300053] using wordTrace_append hprefix tailTrace_300053
  have hstable : (prefixWord ++ tailWord_300053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300053).length < 2 ^ (prefixWord ++ tailWord_300053).sum := by decide
  have hdescent : baseEnd_300053 < baseStart_300053 := by decide
  rcases family_descends (prefixWord ++ tailWord_300053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300060 : List Nat := [2, 2, 3, 1, 4, 1, 2, 5]
def baseStart_300060 : Nat := 118140960795 + 300060 * 2 ^ 59
def prefixEnd_300060 : Nat := 4983230072969 + 3 ^ 40 * 300060 * 2
def baseEnd_300060 : Nat := 45651853389096665946683

theorem tailTrace_300060 : CollatzResearch.WordTrace tailWord_300060 prefixEnd_300060 45651853389096665946683 := by
  unfold tailWord_300060
  simp only [CollatzResearch.WordTrace]
  refine ⟨5472043646470670506596817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7296058195294227342129089 5472043646470670506596817)
  ·
    refine ⟨4104032734853002879947613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5472043646470670506596817 4104032734853002879947613)
    ·
      refine ⟨1539012275569876079980355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4104032734853002879947613 1539012275569876079980355)
      ·
        refine ⟨2308518413354814119970533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1539012275569876079980355 2308518413354814119970533)
        ·
          refine ⟨432847202504027647494475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2308518413354814119970533 432847202504027647494475)
          ·
            refine ⟨649270803756041471241713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432847202504027647494475 649270803756041471241713)
            ·
              refine ⟨486953102817031103431285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 649270803756041471241713 486953102817031103431285)
              ·
                refine ⟨45651853389096665946683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 486953102817031103431285 45651853389096665946683)
                ·
                  rfl

theorem cell20_300060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 5].length) (baseStart_300060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300060 prefixEnd_300060 := by exact prefixLift 300060
  have htrace : WordTrace (prefixWord ++ tailWord_300060) baseStart_300060 baseEnd_300060 := by
    simpa [prefixWord, tailWord_300060, baseEnd_300060] using wordTrace_append hprefix tailTrace_300060
  have hstable : (prefixWord ++ tailWord_300060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300060).length < 2 ^ (prefixWord ++ tailWord_300060).sum := by decide
  have hdescent : baseEnd_300060 < baseStart_300060 := by decide
  rcases family_descends (prefixWord ++ tailWord_300060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300067 : List Nat := [1, 1, 1, 4, 3, 3, 1, 3, 3]
def baseStart_300067 : Nat := 118140960795 + 300067 * 2 ^ 59
def prefixEnd_300067 : Nat := 4983230072969 + 3 ^ 40 * 300067 * 2
def baseEnd_300067 : Nat := 136958755158029084606687

theorem tailTrace_300067 : CollatzResearch.WordTrace tailWord_300067 prefixEnd_300067 136958755158029084606687 := by
  unfold tailWord_300067
  simp only [CollatzResearch.WordTrace]
  refine ⟨10944342603915981208698455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7296228402610654139132303 10944342603915981208698455)
  ·
    refine ⟨16416513905873971813047683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10944342603915981208698455 16416513905873971813047683)
    ·
      refine ⟨24624770858810957719571525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16416513905873971813047683 24624770858810957719571525)
      ·
        refine ⟨4617144536027054572419661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24624770858810957719571525 4617144536027054572419661)
        ·
          refine ⟨1731429201010145464657373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4617144536027054572419661 1731429201010145464657373)
          ·
            refine ⟨649285950378804549246515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1731429201010145464657373 649285950378804549246515)
            ·
              refine ⟨973928925568206823869773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 649285950378804549246515 973928925568206823869773)
              ·
                refine ⟨365223347088077558951165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 973928925568206823869773 365223347088077558951165)
                ·
                  refine ⟨136958755158029084606687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 365223347088077558951165 136958755158029084606687)
                  ·
                    rfl

theorem cell20_300067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 3].length) (baseStart_300067 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300067 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300067 prefixEnd_300067 := by exact prefixLift 300067
  have htrace : WordTrace (prefixWord ++ tailWord_300067) baseStart_300067 baseEnd_300067 := by
    simpa [prefixWord, tailWord_300067, baseEnd_300067] using wordTrace_append hprefix tailTrace_300067
  have hstable : (prefixWord ++ tailWord_300067).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300067).length < 2 ^ (prefixWord ++ tailWord_300067).sum := by decide
  have hdescent : baseEnd_300067 < baseStart_300067 := by decide
  rcases family_descends (prefixWord ++ tailWord_300067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300150 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_300150 : Nat := 118140960795 + 300150 * 2 ^ 59
def prefixEnd_300150 : Nat := 4983230072969 + 3 ^ 40 * 300150 * 2
def baseEnd_300150 : Nat := 136996638619649684839681

theorem tailTrace_300150 : CollatzResearch.WordTrace tailWord_300150 prefixEnd_300150 136996638619649684839681 := by
  unfold tailWord_300150
  simp only [CollatzResearch.WordTrace]
  refine ⟨684210616413455398998119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7298246575076857589313269 684210616413455398998119)
  ·
    refine ⟨1026315924620183098497179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 684210616413455398998119 1026315924620183098497179)
    ·
      refine ⟨1539473886930274647745769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1026315924620183098497179 1539473886930274647745769)
      ·
        refine ⟨1154605415197705985809327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1539473886930274647745769 1154605415197705985809327)
        ·
          refine ⟨1731908122796558978713991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1154605415197705985809327 1731908122796558978713991)
          ·
            refine ⟨2597862184194838468070987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1731908122796558978713991 2597862184194838468070987)
            ·
              refine ⟨3896793276292257702106481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2597862184194838468070987 3896793276292257702106481)
              ·
                refine ⟨2922594957219193276579861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3896793276292257702106481 2922594957219193276579861)
                ·
                  refine ⟨136996638619649684839681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2922594957219193276579861 136996638619649684839681)
                  ·
                    rfl

theorem cell20_300150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_300150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300150 prefixEnd_300150 := by exact prefixLift 300150
  have htrace : WordTrace (prefixWord ++ tailWord_300150) baseStart_300150 baseEnd_300150 := by
    simpa [prefixWord, tailWord_300150, baseEnd_300150] using wordTrace_append hprefix tailTrace_300150
  have hstable : (prefixWord ++ tailWord_300150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300150).length < 2 ^ (prefixWord ++ tailWord_300150).sum := by decide
  have hdescent : baseEnd_300150 < baseStart_300150 := by decide
  rcases family_descends (prefixWord ++ tailWord_300150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300188 : List Nat := [2, 2, 3, 2, 1, 2, 2, 2, 4]
def baseStart_300188 : Nat := 118140960795 + 300188 * 2 ^ 59
def prefixEnd_300188 : Nat := 4983230072969 + 3 ^ 40 * 300188 * 2
def baseEnd_300188 : Nat := 137013982855090441572859

theorem tailTrace_300188 : CollatzResearch.WordTrace tailWord_300188 prefixEnd_300188 137013982855090441572859 := by
  unfold tailWord_300188
  simp only [CollatzResearch.WordTrace]
  refine ⟨5474377918238809436926609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7299170557651745915902145 5474377918238809436926609)
  ·
    refine ⟨4105783438679107077694957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5474377918238809436926609 4105783438679107077694957)
    ·
      refine ⟨1539668789504665154135609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4105783438679107077694957 1539668789504665154135609)
      ·
        refine ⟨1154751592128498865601707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1539668789504665154135609 1154751592128498865601707)
        ·
          refine ⟨1732127388192748298402561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1154751592128498865601707 1732127388192748298402561)
          ·
            refine ⟨1299095541144561223801921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1732127388192748298402561 1299095541144561223801921)
            ·
              refine ⟨974321655858420917851441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1299095541144561223801921 974321655858420917851441)
              ·
                refine ⟨730741241893815688388581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 974321655858420917851441 730741241893815688388581)
                ·
                  refine ⟨137013982855090441572859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 730741241893815688388581 137013982855090441572859)
                  ·
                    rfl

theorem cell20_300188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_300188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300188 prefixEnd_300188 := by exact prefixLift 300188
  have htrace : WordTrace (prefixWord ++ tailWord_300188) baseStart_300188 baseEnd_300188 := by
    simpa [prefixWord, tailWord_300188, baseEnd_300188] using wordTrace_append hprefix tailTrace_300188
  have hstable : (prefixWord ++ tailWord_300188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300188).length < 2 ^ (prefixWord ++ tailWord_300188).sum := by decide
  have hdescent : baseEnd_300188 < baseStart_300188 := by decide
  rcases family_descends (prefixWord ++ tailWord_300188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300191 : List Nat := [1, 1, 2, 6, 2, 2, 2, 4]
def baseStart_300191 : Nat := 118140960795 + 300191 * 2 ^ 59
def prefixEnd_300191 : Nat := 4983230072969 + 3 ^ 40 * 300191 * 2
def baseEnd_300191 : Nat := 45671784045611921490949

theorem tailTrace_300191 : CollatzResearch.WordTrace tailWord_300191 prefixEnd_300191 45671784045611921490949 := by
  unfold tailWord_300191
  simp only [CollatzResearch.WordTrace]
  refine ⟨10948865255466750386212427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7299243503644500257474951 10948865255466750386212427)
  ·
    refine ⟨16423297883200125579318641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10948865255466750386212427 16423297883200125579318641)
    ·
      refine ⟨12317473412400094184488981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16423297883200125579318641 12317473412400094184488981)
      ·
        refine ⟨577381566206254414897921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12317473412400094184488981 577381566206254414897921)
        ·
          refine ⟨433036174654690811173441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 577381566206254414897921 433036174654690811173441)
          ·
            refine ⟨324777130991018108380081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 433036174654690811173441 324777130991018108380081)
            ·
              refine ⟨243582848243263581285061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 324777130991018108380081 243582848243263581285061)
              ·
                refine ⟨45671784045611921490949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 243582848243263581285061 45671784045611921490949)
                ·
                  rfl

theorem cell20_300191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 4].length) (baseStart_300191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300191 prefixEnd_300191 := by exact prefixLift 300191
  have htrace : WordTrace (prefixWord ++ tailWord_300191) baseStart_300191 baseEnd_300191 := by
    simpa [prefixWord, tailWord_300191, baseEnd_300191] using wordTrace_append hprefix tailTrace_300191
  have hstable : (prefixWord ++ tailWord_300191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300191).length < 2 ^ (prefixWord ++ tailWord_300191).sum := by decide
  have hdescent : baseEnd_300191 < baseStart_300191 := by decide
  rcases family_descends (prefixWord ++ tailWord_300191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300247 : List Nat := [1, 1, 3, 2, 1, 2, 2, 4, 4]
def baseStart_300247 : Nat := 118140960795 + 300247 * 2 ^ 59
def prefixEnd_300247 : Nat := 4983230072969 + 3 ^ 40 * 300247 * 2
def baseEnd_300247 : Nat := 137040912062748458605951

theorem tailTrace_300247 : CollatzResearch.WordTrace tailWord_300247 prefixEnd_300247 137040912062748458605951 := by
  unfold tailWord_300247
  simp only [CollatzResearch.WordTrace]
  refine ⟨10950907743263871950250995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7300605162175914633500663 10950907743263871950250995)
  ·
    refine ⟨16426361614895807925376493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10950907743263871950250995 16426361614895807925376493)
    ·
      refine ⟨6159885605585927972016185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16426361614895807925376493 6159885605585927972016185)
      ·
        refine ⟨4619914204189445979012139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6159885605585927972016185 4619914204189445979012139)
        ·
          refine ⟨6929871306284168968518209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4619914204189445979012139 6929871306284168968518209)
          ·
            refine ⟨5197403479713126726388657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6929871306284168968518209 5197403479713126726388657)
            ·
              refine ⟨3898052609784845044791493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5197403479713126726388657 3898052609784845044791493)
              ·
                refine ⟨730884864334658445898405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3898052609784845044791493 730884864334658445898405)
                ·
                  refine ⟨137040912062748458605951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 730884864334658445898405 137040912062748458605951)
                  ·
                    rfl

theorem cell20_300247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 4].length) (baseStart_300247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300247 prefixEnd_300247 := by exact prefixLift 300247
  have htrace : WordTrace (prefixWord ++ tailWord_300247) baseStart_300247 baseEnd_300247 := by
    simpa [prefixWord, tailWord_300247, baseEnd_300247] using wordTrace_append hprefix tailTrace_300247
  have hstable : (prefixWord ++ tailWord_300247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300247).length < 2 ^ (prefixWord ++ tailWord_300247).sum := by decide
  have hdescent : baseEnd_300247 < baseStart_300247 := by decide
  rcases family_descends (prefixWord ++ tailWord_300247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300271 : List Nat := [1, 1, 2, 1, 8, 7]
def baseStart_300271 : Nat := 118140960795 + 300271 * 2 ^ 59
def prefixEnd_300271 : Nat := 4983230072969 + 3 ^ 40 * 300271 * 2
def baseEnd_300271 : Nat := 5075995048767075622439

theorem tailTrace_300271 : CollatzResearch.WordTrace tailWord_300271 prefixEnd_300271 5075995048767075622439 := by
  unfold tailWord_300271
  simp only [CollatzResearch.WordTrace]
  refine ⟨10951783095176924049124667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7301188730117949366083111 10951783095176924049124667)
  ·
    refine ⟨16427674642765386073687001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10951783095176924049124667 16427674642765386073687001)
    ·
      refine ⟨12320755982074039555265251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16427674642765386073687001 12320755982074039555265251)
      ·
        refine ⟨18481133973111059332897877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12320755982074039555265251 18481133973111059332897877)
        ·
          refine ⟨216575788747395226557397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 18481133973111059332897877 216575788747395226557397)
          ·
            refine ⟨5075995048767075622439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 216575788747395226557397 5075995048767075622439)
            ·
              rfl

theorem cell20_300271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 7].length) (baseStart_300271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300271 prefixEnd_300271 := by exact prefixLift 300271
  have htrace : WordTrace (prefixWord ++ tailWord_300271) baseStart_300271 baseEnd_300271 := by
    simpa [prefixWord, tailWord_300271, baseEnd_300271] using wordTrace_append hprefix tailTrace_300271
  have hstable : (prefixWord ++ tailWord_300271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300271).length < 2 ^ (prefixWord ++ tailWord_300271).sum := by decide
  have hdescent : baseEnd_300271 < baseStart_300271 := by decide
  rcases family_descends (prefixWord ++ tailWord_300271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300274 : List Nat := [3, 2, 1, 3, 3, 1, 2, 2, 3]
def baseStart_300274 : Nat := 118140960795 + 300274 * 2 ^ 59
def prefixEnd_300274 : Nat := 4983230072969 + 3 ^ 40 * 300274 * 2
def baseEnd_300274 : Nat := 137053235598456364705841

theorem tailTrace_300274 : CollatzResearch.WordTrace tailWord_300274 prefixEnd_300274 137053235598456364705841 := by
  unfold tailWord_300274
  simp only [CollatzResearch.WordTrace]
  refine ⟨2737973128541513890370969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7301261676110703707655917 2737973128541513890370969)
  ·
    refine ⟨2053479846406135417778227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2737973128541513890370969 2053479846406135417778227)
    ·
      refine ⟨3080219769609203126667341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2053479846406135417778227 3080219769609203126667341)
      ·
        refine ⟨1155082413603451172500253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3080219769609203126667341 1155082413603451172500253)
        ·
          refine ⟨433155905101294189687595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1155082413603451172500253 433155905101294189687595)
          ·
            refine ⟨649733857651941284531393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433155905101294189687595 649733857651941284531393)
            ·
              refine ⟨487300393238955963398545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 649733857651941284531393 487300393238955963398545)
              ·
                refine ⟨365475294929216972548909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 487300393238955963398545 365475294929216972548909)
                ·
                  refine ⟨137053235598456364705841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 365475294929216972548909 137053235598456364705841)
                  ·
                    rfl

theorem cell20_300274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_300274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300274 prefixEnd_300274 := by exact prefixLift 300274
  have htrace : WordTrace (prefixWord ++ tailWord_300274) baseStart_300274 baseEnd_300274 := by
    simpa [prefixWord, tailWord_300274, baseEnd_300274] using wordTrace_append hprefix tailTrace_300274
  have hstable : (prefixWord ++ tailWord_300274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300274).length < 2 ^ (prefixWord ++ tailWord_300274).sum := by decide
  have hdescent : baseEnd_300274 < baseStart_300274 := by decide
  rcases family_descends (prefixWord ++ tailWord_300274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300302 : List Nat := [4, 1, 1, 2, 1, 4, 1, 2, 4]
def baseStart_300302 : Nat := 118140960795 + 300302 * 2 ^ 59
def prefixEnd_300302 : Nat := 4983230072969 + 3 ^ 40 * 300302 * 2
def baseEnd_300302 : Nat := 137066015561412711772393

theorem tailTrace_300302 : CollatzResearch.WordTrace tailWord_300302 prefixEnd_300302 137066015561412711772393 := by
  unfold tailWord_300302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1369114219758077042937895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7301942505376410895668773 1369114219758077042937895)
  ·
    refine ⟨2053671329637115564406843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1369114219758077042937895 2053671329637115564406843)
    ·
      refine ⟨3080506994455673346610265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2053671329637115564406843 3080506994455673346610265)
      ·
        refine ⟨2310380245841755009957699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3080506994455673346610265 2310380245841755009957699)
        ·
          refine ⟨3465570368762632514936549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2310380245841755009957699 3465570368762632514936549)
          ·
            refine ⟨649794444142993596550603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3465570368762632514936549 649794444142993596550603)
            ·
              refine ⟨974691666214490394825905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 649794444142993596550603 974691666214490394825905)
              ·
                refine ⟨731018749660867796119429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 974691666214490394825905 731018749660867796119429)
                ·
                  refine ⟨137066015561412711772393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 731018749660867796119429 137066015561412711772393)
                  ·
                    rfl

theorem cell20_300302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_300302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300302 prefixEnd_300302 := by exact prefixLift 300302
  have htrace : WordTrace (prefixWord ++ tailWord_300302) baseStart_300302 baseEnd_300302 := by
    simpa [prefixWord, tailWord_300302, baseEnd_300302] using wordTrace_append hprefix tailTrace_300302
  have hstable : (prefixWord ++ tailWord_300302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300302).length < 2 ^ (prefixWord ++ tailWord_300302).sum := by decide
  have hdescent : baseEnd_300302 < baseStart_300302 := by decide
  rcases family_descends (prefixWord ++ tailWord_300302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300350 : List Nat := [4, 2, 1, 2, 1, 1, 5, 1, 3]
def baseStart_300350 : Nat := 118140960795 + 300350 * 2 ^ 59
def prefixEnd_300350 : Nat := 4983230072969 + 3 ^ 40 * 300350 * 2
def baseEnd_300350 : Nat := 137087924069337878172197

theorem tailTrace_300350 : CollatzResearch.WordTrace tailWord_300350 prefixEnd_300350 137087924069337878172197 := by
  unfold tailWord_300350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1369333057736340067656313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7303109641260480360833669 1369333057736340067656313)
  ·
    refine ⟨1026999793302255050742235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1369333057736340067656313 1026999793302255050742235)
    ·
      refine ⟨1540499689953382576113353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1026999793302255050742235 1540499689953382576113353)
      ·
        refine ⟨1155374767465036932085015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1540499689953382576113353 1155374767465036932085015)
        ·
          refine ⟨1733062151197555398127523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1155374767465036932085015 1733062151197555398127523)
          ·
            refine ⟨2599593226796333097191285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1733062151197555398127523 2599593226796333097191285)
            ·
              refine ⟨243711865012156227861683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2599593226796333097191285 243711865012156227861683)
              ·
                refine ⟨365567797518234341792525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243711865012156227861683 365567797518234341792525)
                ·
                  refine ⟨137087924069337878172197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 365567797518234341792525 137087924069337878172197)
                  ·
                    rfl

theorem cell20_300350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_300350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300350 prefixEnd_300350 := by exact prefixLift 300350
  have htrace : WordTrace (prefixWord ++ tailWord_300350) baseStart_300350 baseEnd_300350 := by
    simpa [prefixWord, tailWord_300350, baseEnd_300350] using wordTrace_append hprefix tailTrace_300350
  have hstable : (prefixWord ++ tailWord_300350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300350).length < 2 ^ (prefixWord ++ tailWord_300350).sum := by decide
  have hdescent : baseEnd_300350 < baseStart_300350 := by decide
  rcases family_descends (prefixWord ++ tailWord_300350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300361 : List Nat := [1, 2, 1, 1, 2, 3, 4, 2, 4]
def baseStart_300361 : Nat := 118140960795 + 300361 * 2 ^ 59
def prefixEnd_300361 : Nat := 4983230072969 + 3 ^ 40 * 300361 * 2
def baseEnd_300361 : Nat := 137092944769070728805485

theorem tailTrace_300361 : CollatzResearch.WordTrace tailWord_300361 prefixEnd_300361 137092944769070728805485 := by
  unfold tailWord_300361
  simp only [CollatzResearch.WordTrace]
  refine ⟨10955065664850869419900937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7303377109900579613267291 10955065664850869419900937)
  ·
    refine ⟨8216299248638152064925703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10955065664850869419900937 8216299248638152064925703)
    ·
      refine ⟨12324448872957228097388555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8216299248638152064925703 12324448872957228097388555)
      ·
        refine ⟨18486673309435842146082833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12324448872957228097388555 18486673309435842146082833)
        ·
          refine ⟨13865004982076881609562125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18486673309435842146082833 13865004982076881609562125)
          ·
            refine ⟨5199376868278830603585797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13865004982076881609562125 5199376868278830603585797)
            ·
              refine ⟨974883162802280738172337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5199376868278830603585797 974883162802280738172337)
              ·
                refine ⟨731162372101710553629253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 974883162802280738172337 731162372101710553629253)
                ·
                  refine ⟨137092944769070728805485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 731162372101710553629253 137092944769070728805485)
                  ·
                    rfl

theorem cell20_300361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_300361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300361 prefixEnd_300361 := by exact prefixLift 300361
  have htrace : WordTrace (prefixWord ++ tailWord_300361) baseStart_300361 baseEnd_300361 := by
    simpa [prefixWord, tailWord_300361, baseEnd_300361] using wordTrace_append hprefix tailTrace_300361
  have hstable : (prefixWord ++ tailWord_300361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300361).length < 2 ^ (prefixWord ++ tailWord_300361).sum := by decide
  have hdescent : baseEnd_300361 < baseStart_300361 := by decide
  rcases family_descends (prefixWord ++ tailWord_300361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300364 : List Nat := [2, 2, 1, 3, 2, 4, 2, 4]
def baseStart_300364 : Nat := 118140960795 + 300364 * 2 ^ 59
def prefixEnd_300364 : Nat := 4983230072969 + 3 ^ 40 * 300364 * 2
def baseEnd_300364 : Nat := 45698104683605350568491

theorem tailTrace_300364 : CollatzResearch.WordTrace tailWord_300364 prefixEnd_300364 45698104683605350568491 := by
  unfold tailWord_300364
  simp only [CollatzResearch.WordTrace]
  refine ⟨5477587541920000466130073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7303450055893333954840097 5477587541920000466130073)
  ·
    refine ⟨4108190656440000349597555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5477587541920000466130073 4108190656440000349597555)
    ·
      refine ⟨6162285984660000524396333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4108190656440000349597555 6162285984660000524396333)
      ·
        refine ⟨2310857244247500196648625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6162285984660000524396333 2310857244247500196648625)
        ·
          refine ⟨1733142933185625147486469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2310857244247500196648625 1733142933185625147486469)
          ·
            refine ⟨324964299972304715153713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1733142933185625147486469 324964299972304715153713)
            ·
              refine ⟨243723224979228536365285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 324964299972304715153713 243723224979228536365285)
              ·
                refine ⟨45698104683605350568491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 243723224979228536365285 45698104683605350568491)
                ·
                  rfl

theorem cell20_300364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 4].length) (baseStart_300364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300364 prefixEnd_300364 := by exact prefixLift 300364
  have htrace : WordTrace (prefixWord ++ tailWord_300364) baseStart_300364 baseEnd_300364 := by
    simpa [prefixWord, tailWord_300364, baseEnd_300364] using wordTrace_append hprefix tailTrace_300364
  have hstable : (prefixWord ++ tailWord_300364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300364).length < 2 ^ (prefixWord ++ tailWord_300364).sum := by decide
  have hdescent : baseEnd_300364 < baseStart_300364 := by decide
  rcases family_descends (prefixWord ++ tailWord_300364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300368 : List Nat := [2, 1, 1, 1, 1, 5, 3, 6]
def baseStart_300368 : Nat := 118140960795 + 300368 * 2 ^ 59
def prefixEnd_300368 : Nat := 4983230072969 + 3 ^ 40 * 300368 * 2
def baseEnd_300368 : Nat := 45698713253269938524041

theorem tailTrace_300368 : CollatzResearch.WordTrace tailWord_300368 prefixEnd_300368 45698713253269938524041 := by
  unfold tailWord_300368
  simp only [CollatzResearch.WordTrace]
  refine ⟨5477660487912754807702879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7303547317217006410270505 5477660487912754807702879)
  ·
    refine ⟨8216490731869132211554319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5477660487912754807702879 8216490731869132211554319)
    ·
      refine ⟨12324736097803698317331479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8216490731869132211554319 12324736097803698317331479)
      ·
        refine ⟨18487104146705547475997219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12324736097803698317331479 18487104146705547475997219)
        ·
          refine ⟨27730656220058321213995829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18487104146705547475997219 27730656220058321213995829)
          ·
            refine ⟨2599749020630467613812109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27730656220058321213995829 2599749020630467613812109)
            ·
              refine ⟨974905882736425355179541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2599749020630467613812109 974905882736425355179541)
              ·
                refine ⟨45698713253269938524041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 974905882736425355179541 45698713253269938524041)
                ·
                  rfl

theorem cell20_300368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 6].length) (baseStart_300368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300368 prefixEnd_300368 := by exact prefixLift 300368
  have htrace : WordTrace (prefixWord ++ tailWord_300368) baseStart_300368 baseEnd_300368 := by
    simpa [prefixWord, tailWord_300368, baseEnd_300368] using wordTrace_append hprefix tailTrace_300368
  have hstable : (prefixWord ++ tailWord_300368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300368).length < 2 ^ (prefixWord ++ tailWord_300368).sum := by decide
  have hdescent : baseEnd_300368 < baseStart_300368 := by decide
  rcases family_descends (prefixWord ++ tailWord_300368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300405 : List Nat := [1, 3, 4, 1, 3, 2, 2, 1, 3]
def baseStart_300405 : Nat := 118140960795 + 300405 * 2 ^ 59
def prefixEnd_300405 : Nat := 4983230072969 + 3 ^ 40 * 300405 * 2
def baseEnd_300405 : Nat := 137113027568002131338639

theorem tailTrace_300405 : CollatzResearch.WordTrace tailWord_300405 prefixEnd_300405 137113027568002131338639 := by
  unfold tailWord_300405
  simp only [CollatzResearch.WordTrace]
  refine ⟨10956670476691464934502669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7304446984460976623001779 10956670476691464934502669)
  ·
    refine ⟨4108751428759299350438501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10956670476691464934502669 4108751428759299350438501)
    ·
      refine ⟨770390892892368628207219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4108751428759299350438501 770390892892368628207219)
      ·
        refine ⟨1155586339338552942310829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 770390892892368628207219 1155586339338552942310829)
        ·
          refine ⟨433344877251957353366561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1155586339338552942310829 433344877251957353366561)
          ·
            refine ⟨325008657938968015024921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 433344877251957353366561 325008657938968015024921)
            ·
              refine ⟨243756493454226011268691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325008657938968015024921 243756493454226011268691)
              ·
                refine ⟨365634740181339016903037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243756493454226011268691 365634740181339016903037)
                ·
                  refine ⟨137113027568002131338639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 365634740181339016903037 137113027568002131338639)
                  ·
                    rfl

theorem cell20_300405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_300405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300405 prefixEnd_300405 := by exact prefixLift 300405
  have htrace : WordTrace (prefixWord ++ tailWord_300405) baseStart_300405 baseEnd_300405 := by
    simpa [prefixWord, tailWord_300405, baseEnd_300405] using wordTrace_append hprefix tailTrace_300405
  have hstable : (prefixWord ++ tailWord_300405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300405).length < 2 ^ (prefixWord ++ tailWord_300405).sum := by decide
  have hdescent : baseEnd_300405 < baseStart_300405 := by decide
  rcases family_descends (prefixWord ++ tailWord_300405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300409 : List Nat := [1, 2, 1, 3, 2, 1, 6, 1, 3]
def baseStart_300409 : Nat := 118140960795 + 300409 * 2 ^ 59
def prefixEnd_300409 : Nat := 4983230072969 + 3 ^ 40 * 300409 * 2
def baseEnd_300409 : Nat := 137114853276995895205289

theorem tailTrace_300409 : CollatzResearch.WordTrace tailWord_300409 prefixEnd_300409 137114853276995895205289 := by
  unfold tailWord_300409
  simp only [CollatzResearch.WordTrace]
  refine ⟨10956816368676973617648281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7304544245784649078432187 10956816368676973617648281)
  ·
    refine ⟨8217612276507730213236211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10956816368676973617648281 8217612276507730213236211)
    ·
      refine ⟨12326418414761595319854317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8217612276507730213236211 12326418414761595319854317)
      ·
        refine ⟨4622406905535598244945369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12326418414761595319854317 4622406905535598244945369)
        ·
          refine ⟨3466805179151698683709027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4622406905535598244945369 3466805179151698683709027)
          ·
            refine ⟨5200207768727548025563541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3466805179151698683709027 5200207768727548025563541)
            ·
              refine ⟨243759739159103813698291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5200207768727548025563541 243759739159103813698291)
              ·
                refine ⟨365639608738655720547437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243759739159103813698291 365639608738655720547437)
                ·
                  refine ⟨137114853276995895205289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 365639608738655720547437 137114853276995895205289)
                  ·
                    rfl

theorem cell20_300409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 3].length) (baseStart_300409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300409 prefixEnd_300409 := by exact prefixLift 300409
  have htrace : WordTrace (prefixWord ++ tailWord_300409) baseStart_300409 baseEnd_300409 := by
    simpa [prefixWord, tailWord_300409, baseEnd_300409] using wordTrace_append hprefix tailTrace_300409
  have hstable : (prefixWord ++ tailWord_300409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300409).length < 2 ^ (prefixWord ++ tailWord_300409).sum := by decide
  have hdescent : baseEnd_300409 < baseStart_300409 := by decide
  rcases family_descends (prefixWord ++ tailWord_300409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300446 : List Nat := [4, 3, 1, 2, 2, 2, 2, 2, 2]
def baseStart_300446 : Nat := 118140960795 + 300446 * 2 ^ 59
def prefixEnd_300446 : Nat := 4983230072969 + 3 ^ 40 * 300446 * 2
def baseEnd_300446 : Nat := 137131741085188210971805

theorem tailTrace_300446 : CollatzResearch.WordTrace tailWord_300446 prefixEnd_300446 137131741085188210971805 := by
  unfold tailWord_300446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1369770733692866117093149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7305443913028619291163461 1369770733692866117093149)
  ·
    refine ⟨513664025134824793909931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1369770733692866117093149 513664025134824793909931)
    ·
      refine ⟨770496037702237190864897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 513664025134824793909931 770496037702237190864897)
      ·
        refine ⟨577872028276677893148673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 770496037702237190864897 577872028276677893148673)
        ·
          refine ⟨433404021207508419861505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 577872028276677893148673 433404021207508419861505)
          ·
            refine ⟨325053015905631314896129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 433404021207508419861505 325053015905631314896129)
            ·
              refine ⟨243789761929223486172097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325053015905631314896129 243789761929223486172097)
              ·
                refine ⟨182842321446917614629073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 243789761929223486172097 182842321446917614629073)
                ·
                  refine ⟨137131741085188210971805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182842321446917614629073 137131741085188210971805)
                  ·
                    rfl

theorem cell20_300446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_300446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300446 prefixEnd_300446 := by exact prefixLift 300446
  have htrace : WordTrace (prefixWord ++ tailWord_300446) baseStart_300446 baseEnd_300446 := by
    simpa [prefixWord, tailWord_300446, baseEnd_300446] using wordTrace_append hprefix tailTrace_300446
  have hstable : (prefixWord ++ tailWord_300446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300446).length < 2 ^ (prefixWord ++ tailWord_300446).sum := by decide
  have hdescent : baseEnd_300446 < baseStart_300446 := by decide
  rcases family_descends (prefixWord ++ tailWord_300446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300447 : List Nat := [1, 1, 2, 5, 1, 3, 2, 2, 3]
def baseStart_300447 : Nat := 118140960795 + 300447 * 2 ^ 59
def prefixEnd_300447 : Nat := 4983230072969 + 3 ^ 40 * 300447 * 2
def baseEnd_300447 : Nat := 137132197512436651938467

theorem tailTrace_300447 : CollatzResearch.WordTrace tailWord_300447 prefixEnd_300447 137132197512436651938467 := by
  unfold tailWord_300447
  simp only [CollatzResearch.WordTrace]
  refine ⟨10958202342539306107531595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7305468228359537405021063 10958202342539306107531595)
  ·
    refine ⟨16437303513808959161297393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10958202342539306107531595 16437303513808959161297393)
    ·
      refine ⟨12327977635356719370973045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16437303513808959161297393 12327977635356719370973045)
      ·
        refine ⟨1155747903314692441028723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12327977635356719370973045 1155747903314692441028723)
        ·
          refine ⟨1733621854972038661543085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1155747903314692441028723 1733621854972038661543085)
          ·
            refine ⟨650108195614514498078657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1733621854972038661543085 650108195614514498078657)
            ·
              refine ⟨487581146710885873558993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 650108195614514498078657 487581146710885873558993)
              ·
                refine ⟨365685860033164405169245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 487581146710885873558993 365685860033164405169245)
                ·
                  refine ⟨137132197512436651938467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 365685860033164405169245 137132197512436651938467)
                  ·
                    rfl

theorem cell20_300447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 3].length) (baseStart_300447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300447 prefixEnd_300447 := by exact prefixLift 300447
  have htrace : WordTrace (prefixWord ++ tailWord_300447) baseStart_300447 baseEnd_300447 := by
    simpa [prefixWord, tailWord_300447, baseEnd_300447] using wordTrace_append hprefix tailTrace_300447
  have hstable : (prefixWord ++ tailWord_300447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300447).length < 2 ^ (prefixWord ++ tailWord_300447).sum := by decide
  have hdescent : baseEnd_300447 < baseStart_300447 := by decide
  rcases family_descends (prefixWord ++ tailWord_300447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300450 : List Nat := [3, 3, 1, 2, 1, 2, 4, 2, 2]
def baseStart_300450 : Nat := 118140960795 + 300450 * 2 ^ 59
def prefixEnd_300450 : Nat := 4983230072969 + 3 ^ 40 * 300450 * 2
def baseEnd_300450 : Nat := 137133566794181974838455

theorem tailTrace_300450 : CollatzResearch.WordTrace tailWord_300450 prefixEnd_300450 137133566794181974838455 := by
  unfold tailWord_300450
  simp only [CollatzResearch.WordTrace]
  refine ⟨2739577940382109404972701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7305541174352291746593869 2739577940382109404972701)
  ·
    refine ⟨1027341727643291026864763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2739577940382109404972701 1027341727643291026864763)
    ·
      refine ⟨1541012591464936540297145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1027341727643291026864763 1541012591464936540297145)
      ·
        refine ⟨1155759443598702405222859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1541012591464936540297145 1155759443598702405222859)
        ·
          refine ⟨1733639165398053607834289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1155759443598702405222859 1733639165398053607834289)
          ·
            refine ⟨1300229374048540205875717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1733639165398053607834289 1300229374048540205875717)
            ·
              refine ⟨243793007634101288601697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1300229374048540205875717 243793007634101288601697)
              ·
                refine ⟨182844755725575966451273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 243793007634101288601697 182844755725575966451273)
                ·
                  refine ⟨137133566794181974838455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182844755725575966451273 137133566794181974838455)
                  ·
                    rfl

theorem cell20_300450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_300450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300450 prefixEnd_300450 := by exact prefixLift 300450
  have htrace : WordTrace (prefixWord ++ tailWord_300450) baseStart_300450 baseEnd_300450 := by
    simpa [prefixWord, tailWord_300450, baseEnd_300450] using wordTrace_append hprefix tailTrace_300450
  have hstable : (prefixWord ++ tailWord_300450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300450).length < 2 ^ (prefixWord ++ tailWord_300450).sum := by decide
  have hdescent : baseEnd_300450 < baseStart_300450 := by decide
  rcases family_descends (prefixWord ++ tailWord_300450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300489 : List Nat := [1, 2, 1, 1, 2, 1, 3, 4, 5]
def baseStart_300489 : Nat := 118140960795 + 300489 * 2 ^ 59
def prefixEnd_300489 : Nat := 4983230072969 + 3 ^ 40 * 300489 * 2
def baseEnd_300489 : Nat := 137151367456871172538295

theorem tailTrace_300489 : CollatzResearch.WordTrace tailWord_300489 prefixEnd_300489 137151367456871172538295 := by
  unfold tailWord_300489
  simp only [CollatzResearch.WordTrace]
  refine ⟨10959734208387147280560521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7306489472258098187040347 10959734208387147280560521)
  ·
    refine ⟨8219800656290360460420391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10959734208387147280560521 8219800656290360460420391)
    ·
      refine ⟨12329700984435540690630587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8219800656290360460420391 12329700984435540690630587)
      ·
        refine ⟨18494551476653311035945881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12329700984435540690630587 18494551476653311035945881)
        ·
          refine ⟨13870913607489983276959411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18494551476653311035945881 13870913607489983276959411)
          ·
            refine ⟨20806370411234974915439117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13870913607489983276959411 20806370411234974915439117)
            ·
              refine ⟨7802388904213115593289669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20806370411234974915439117 7802388904213115593289669)
              ·
                refine ⟨1462947919539959173741813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7802388904213115593289669 1462947919539959173741813)
                ·
                  refine ⟨137151367456871172538295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1462947919539959173741813 137151367456871172538295)
                  ·
                    rfl

theorem cell20_300489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_300489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300489 prefixEnd_300489 := by exact prefixLift 300489
  have htrace : WordTrace (prefixWord ++ tailWord_300489) baseStart_300489 baseEnd_300489 := by
    simpa [prefixWord, tailWord_300489, baseEnd_300489] using wordTrace_append hprefix tailTrace_300489
  have hstable : (prefixWord ++ tailWord_300489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300489).length < 2 ^ (prefixWord ++ tailWord_300489).sum := by decide
  have hdescent : baseEnd_300489 < baseStart_300489 := by decide
  rcases family_descends (prefixWord ++ tailWord_300489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300502 : List Nat := [5, 2, 1, 1, 1, 2, 3, 2, 3]
def baseStart_300502 : Nat := 118140960795 + 300502 * 2 ^ 59
def prefixEnd_300502 : Nat := 4983230072969 + 3 ^ 40 * 300502 * 2
def baseEnd_300502 : Nat := 137157301011100905104909

theorem tailTrace_300502 : CollatzResearch.WordTrace tailWord_300502 prefixEnd_300502 137157301011100905104909 := by
  unfold tailWord_300502
  simp only [CollatzResearch.WordTrace]
  refine ⟨685013022333753156298985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7306805571560033667189173 685013022333753156298985)
  ·
    refine ⟨513759766750314867224239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 685013022333753156298985 513759766750314867224239)
    ·
      refine ⟨770639650125472300836359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 513759766750314867224239 770639650125472300836359)
      ·
        refine ⟨1155959475188208451254539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 770639650125472300836359 1155959475188208451254539)
        ·
          refine ⟨1733939212782312676881809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1155959475188208451254539 1733939212782312676881809)
          ·
            refine ⟨1300454409586734507661357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1733939212782312676881809 1300454409586734507661357)
            ·
              refine ⟨487670403595025440373009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1300454409586734507661357 487670403595025440373009)
              ·
                refine ⟨365752802696269080279757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 487670403595025440373009 365752802696269080279757)
                ·
                  refine ⟨137157301011100905104909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 365752802696269080279757 137157301011100905104909)
                  ·
                    rfl

theorem cell20_300502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_300502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300502 prefixEnd_300502 := by exact prefixLift 300502
  have htrace : WordTrace (prefixWord ++ tailWord_300502) baseStart_300502 baseEnd_300502 := by
    simpa [prefixWord, tailWord_300502, baseEnd_300502] using wordTrace_append hprefix tailTrace_300502
  have hstable : (prefixWord ++ tailWord_300502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300502).length < 2 ^ (prefixWord ++ tailWord_300502).sum := by decide
  have hdescent : baseEnd_300502 < baseStart_300502 := by decide
  rcases family_descends (prefixWord ++ tailWord_300502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300506 : List Nat := [3, 1, 1, 2, 3, 3, 1, 1, 5]
def baseStart_300506 : Nat := 118140960795 + 300506 * 2 ^ 59
def prefixEnd_300506 : Nat := 4983230072969 + 3 ^ 40 * 300506 * 2
def baseEnd_300506 : Nat := 137159126720094668971559

theorem tailTrace_300506 : CollatzResearch.WordTrace tailWord_300506 prefixEnd_300506 137159126720094668971559 := by
  unfold tailWord_300506
  simp only [CollatzResearch.WordTrace]
  refine ⟨2740088562331389795982343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7306902832883706122619581 2740088562331389795982343)
  ·
    refine ⟨4110132843497084693973515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2740088562331389795982343 4110132843497084693973515)
    ·
      refine ⟨6165199265245627040960273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4110132843497084693973515 6165199265245627040960273)
      ·
        refine ⟨4623899448934220280720205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6165199265245627040960273 4623899448934220280720205)
        ·
          refine ⟨1733962293350332605270077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4623899448934220280720205 1733962293350332605270077)
          ·
            refine ⟨650235860006374726976279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1733962293350332605270077 650235860006374726976279)
            ·
              refine ⟨975353790009562090464419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 650235860006374726976279 975353790009562090464419)
              ·
                refine ⟨1463030685014343135696629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 975353790009562090464419 1463030685014343135696629)
                ·
                  refine ⟨137159126720094668971559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1463030685014343135696629 137159126720094668971559)
                  ·
                    rfl

theorem cell20_300506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_300506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300506 prefixEnd_300506 := by exact prefixLift 300506
  have htrace : WordTrace (prefixWord ++ tailWord_300506) baseStart_300506 baseEnd_300506 := by
    simpa [prefixWord, tailWord_300506, baseEnd_300506] using wordTrace_append hprefix tailTrace_300506
  have hstable : (prefixWord ++ tailWord_300506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300506).length < 2 ^ (prefixWord ++ tailWord_300506).sum := by decide
  have hdescent : baseEnd_300506 < baseStart_300506 := by decide
  rcases family_descends (prefixWord ++ tailWord_300506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300509 : List Nat := [1, 4, 3, 1, 1, 2, 2, 4, 2]
def baseStart_300509 : Nat := 118140960795 + 300509 * 2 ^ 59
def prefixEnd_300509 : Nat := 4983230072969 + 3 ^ 40 * 300509 * 2
def baseEnd_300509 : Nat := 137160496001839991871547

theorem tailTrace_300509 : CollatzResearch.WordTrace tailWord_300509 prefixEnd_300509 137160496001839991871547 := by
  unfold tailWord_300509
  simp only [CollatzResearch.WordTrace]
  refine ⟨10960463668314690696288581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7306975778876460464192387 10960463668314690696288581)
  ·
    refine ⟨2055086937809004505554109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10960463668314690696288581 2055086937809004505554109)
    ·
      refine ⟨770657601678376689582791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2055086937809004505554109 770657601678376689582791)
      ·
        refine ⟨1155986402517565034374187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 770657601678376689582791 1155986402517565034374187)
        ·
          refine ⟨1733979603776347551561281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1155986402517565034374187 1733979603776347551561281)
          ·
            refine ⟨1300484702832260663670961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1733979603776347551561281 1300484702832260663670961)
            ·
              refine ⟨975363527124195497753221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1300484702832260663670961 975363527124195497753221)
              ·
                refine ⟨182880661335786655828729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 975363527124195497753221 182880661335786655828729)
                ·
                  refine ⟨137160496001839991871547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182880661335786655828729 137160496001839991871547)
                  ·
                    rfl

theorem cell20_300509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_300509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300509 prefixEnd_300509 := by exact prefixLift 300509
  have htrace : WordTrace (prefixWord ++ tailWord_300509) baseStart_300509 baseEnd_300509 := by
    simpa [prefixWord, tailWord_300509, baseEnd_300509] using wordTrace_append hprefix tailTrace_300509
  have hstable : (prefixWord ++ tailWord_300509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300509).length < 2 ^ (prefixWord ++ tailWord_300509).sum := by decide
  have hdescent : baseEnd_300509 < baseStart_300509 := by decide
  rcases family_descends (prefixWord ++ tailWord_300509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300513 : List Nat := [1, 2, 3, 1, 2, 3, 1, 3, 4]
def baseStart_300513 : Nat := 118140960795 + 300513 * 2 ^ 59
def prefixEnd_300513 : Nat := 4983230072969 + 3 ^ 40 * 300513 * 2
def baseEnd_300513 : Nat := 137162321710833755738197

theorem tailTrace_300513 : CollatzResearch.WordTrace tailWord_300513 prefixEnd_300513 137162321710833755738197 := by
  unfold tailWord_300513
  simp only [CollatzResearch.WordTrace]
  refine ⟨10960609560300199379434193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7307073040200132919622795 10960609560300199379434193)
  ·
    refine ⟨8220457170225149534575645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10960609560300199379434193 8220457170225149534575645)
    ·
      refine ⟨3082671438834431075465867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8220457170225149534575645 3082671438834431075465867)
      ·
        refine ⟨4624007158251646613198801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3082671438834431075465867 4624007158251646613198801)
        ·
          refine ⟨3468005368688734959899101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4624007158251646613198801 3468005368688734959899101)
          ·
            refine ⟨1300502013258275609962163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3468005368688734959899101 1300502013258275609962163)
            ·
              refine ⟨1950753019887413414943245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1300502013258275609962163 1950753019887413414943245)
              ·
                refine ⟨731532382457780030603717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1950753019887413414943245 731532382457780030603717)
                ·
                  refine ⟨137162321710833755738197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 731532382457780030603717 137162321710833755738197)
                  ·
                    rfl

theorem cell20_300513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_300513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300513 prefixEnd_300513 := by exact prefixLift 300513
  have htrace : WordTrace (prefixWord ++ tailWord_300513) baseStart_300513 baseEnd_300513 := by
    simpa [prefixWord, tailWord_300513, baseEnd_300513] using wordTrace_append hprefix tailTrace_300513
  have hstable : (prefixWord ++ tailWord_300513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300513).length < 2 ^ (prefixWord ++ tailWord_300513).sum := by decide
  have hdescent : baseEnd_300513 < baseStart_300513 := by decide
  rcases family_descends (prefixWord ++ tailWord_300513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300520 : List Nat := [2, 1, 4, 1, 1, 2, 2, 7]
def baseStart_300520 : Nat := 118140960795 + 300520 * 2 ^ 59
def prefixEnd_300520 : Nat := 4983230072969 + 3 ^ 40 * 300520 * 2
def baseEnd_300520 : Nat := 45721838900524280834945

theorem tailTrace_300520 : CollatzResearch.WordTrace tailWord_300520 prefixEnd_300520 45721838900524280834945 := by
  unfold tailWord_300520
  simp only [CollatzResearch.WordTrace]
  refine ⟨5480432435637419787469507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7307243247516559716626009 5480432435637419787469507)
  ·
    refine ⟨8220648653456129681204261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5480432435637419787469507 8220648653456129681204261)
    ·
      refine ⟨1541371622523024315225799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8220648653456129681204261 1541371622523024315225799)
      ·
        refine ⟨2312057433784536472838699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1541371622523024315225799 2312057433784536472838699)
        ·
          refine ⟨3468086150676804709258049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2312057433784536472838699 3468086150676804709258049)
          ·
            refine ⟨2601064613007603531943537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3468086150676804709258049 2601064613007603531943537)
            ·
              refine ⟨1950798459755702648957653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2601064613007603531943537 1950798459755702648957653)
              ·
                refine ⟨45721838900524280834945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1950798459755702648957653 45721838900524280834945)
                ·
                  rfl

theorem cell20_300520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 7].length) (baseStart_300520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300520 prefixEnd_300520 := by exact prefixLift 300520
  have htrace : WordTrace (prefixWord ++ tailWord_300520) baseStart_300520 baseEnd_300520 := by
    simpa [prefixWord, tailWord_300520, baseEnd_300520] using wordTrace_append hprefix tailTrace_300520
  have hstable : (prefixWord ++ tailWord_300520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300520).length < 2 ^ (prefixWord ++ tailWord_300520).sum := by decide
  have hdescent : baseEnd_300520 < baseStart_300520 := by decide
  rcases family_descends (prefixWord ++ tailWord_300520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300530 : List Nat := [3, 2, 1, 4, 1, 1, 2, 2, 4]
def baseStart_300530 : Nat := 118140960795 + 300530 * 2 ^ 59
def prefixEnd_300530 : Nat := 4983230072969 + 3 ^ 40 * 300530 * 2
def baseEnd_300530 : Nat := 137170080974057252171461

theorem tailTrace_300530 : CollatzResearch.WordTrace tailWord_300530 prefixEnd_300530 137170080974057252171461 := by
  unfold tailWord_300530
  simp only [CollatzResearch.WordTrace]
  refine ⟨2740307400309652820700761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7307486400825740855202029 2740307400309652820700761)
  ·
    refine ⟨2055230550232239615525571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2740307400309652820700761 2055230550232239615525571)
    ·
      refine ⟨3082845825348359423288357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2055230550232239615525571 3082845825348359423288357)
      ·
        refine ⟨578033592252817391866567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3082845825348359423288357 578033592252817391866567)
        ·
          refine ⟨867050388379226087799851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 578033592252817391866567 867050388379226087799851)
          ·
            refine ⟨1300575582568839131699777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 867050388379226087799851 1300575582568839131699777)
            ·
              refine ⟨975431686926629348774833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1300575582568839131699777 975431686926629348774833)
              ·
                refine ⟨731573765194972011581125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 975431686926629348774833 731573765194972011581125)
                ·
                  refine ⟨137170080974057252171461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 731573765194972011581125 137170080974057252171461)
                  ·
                    rfl

theorem cell20_300530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_300530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300530 prefixEnd_300530 := by exact prefixLift 300530
  have htrace : WordTrace (prefixWord ++ tailWord_300530) baseStart_300530 baseEnd_300530 := by
    simpa [prefixWord, tailWord_300530, baseEnd_300530] using wordTrace_append hprefix tailTrace_300530
  have hstable : (prefixWord ++ tailWord_300530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300530).length < 2 ^ (prefixWord ++ tailWord_300530).sum := by decide
  have hdescent : baseEnd_300530 < baseStart_300530 := by decide
  rcases family_descends (prefixWord ++ tailWord_300530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300533 : List Nat := [1, 3, 5, 1, 1, 3, 2, 4]
def baseStart_300533 : Nat := 118140960795 + 300533 * 2 ^ 59
def prefixEnd_300533 : Nat := 4983230072969 + 3 ^ 40 * 300533 * 2
def baseEnd_300533 : Nat := 45723816751934191690483

theorem tailTrace_300533 : CollatzResearch.WordTrace tailWord_300533 prefixEnd_300533 45723816751934191690483 := by
  unfold tailWord_300533
  simp only [CollatzResearch.WordTrace]
  refine ⟨10961339020227742795162253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7307559346818495196774835 10961339020227742795162253)
  ·
    refine ⟨4110502132585403548185845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10961339020227742795162253 4110502132585403548185845)
    ·
      refine ⟨385359574929881582642423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4110502132585403548185845 385359574929881582642423)
      ·
        refine ⟨578039362394822373963635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385359574929881582642423 578039362394822373963635)
        ·
          refine ⟨867059043592233560945453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 578039362394822373963635 867059043592233560945453)
          ·
            refine ⟨325147141347087585354545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 867059043592233560945453 325147141347087585354545)
            ·
              refine ⟨243860356010315689015909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325147141347087585354545 243860356010315689015909)
              ·
                refine ⟨45723816751934191690483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 243860356010315689015909 45723816751934191690483)
                ·
                  rfl

theorem cell20_300533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 4].length) (baseStart_300533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300533 prefixEnd_300533 := by exact prefixLift 300533
  have htrace : WordTrace (prefixWord ++ tailWord_300533) baseStart_300533 baseEnd_300533 := by
    simpa [prefixWord, tailWord_300533, baseEnd_300533] using wordTrace_append hprefix tailTrace_300533
  have hstable : (prefixWord ++ tailWord_300533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300533).length < 2 ^ (prefixWord ++ tailWord_300533).sum := by decide
  have hdescent : baseEnd_300533 < baseStart_300533 := by decide
  rcases family_descends (prefixWord ++ tailWord_300533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300550 : List Nat := [6, 2, 1, 1, 2, 2, 6]
def baseStart_300550 : Nat := 118140960795 + 300550 * 2 ^ 59
def prefixEnd_300550 : Nat := 4983230072969 + 3 ^ 40 * 300550 * 2
def baseEnd_300550 : Nat := 15242134391002896833857

theorem tailTrace_300550 : CollatzResearch.WordTrace tailWord_300550 prefixEnd_300550 15242134391002896833857 := by
  unfold tailWord_300550
  simp only [CollatzResearch.WordTrace]
  refine ⟨342561220661442334329097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7307972707444103132354069 342561220661442334329097)
  ·
    refine ⟨256920915496081750746823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 342561220661442334329097 256920915496081750746823)
    ·
      refine ⟨385381373244122626120235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256920915496081750746823 385381373244122626120235)
      ·
        refine ⟨578072059866183939180353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385381373244122626120235 578072059866183939180353)
        ·
          refine ⟨433554044899637954385265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 578072059866183939180353 433554044899637954385265)
          ·
            refine ⟨325165533674728465788949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 433554044899637954385265 325165533674728465788949)
            ·
              refine ⟨15242134391002896833857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 325165533674728465788949 15242134391002896833857)
              ·
                rfl

theorem cell20_300550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 6].length) (baseStart_300550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300550 prefixEnd_300550 := by exact prefixLift 300550
  have htrace : WordTrace (prefixWord ++ tailWord_300550) baseStart_300550 baseEnd_300550 := by
    simpa [prefixWord, tailWord_300550, baseEnd_300550] using wordTrace_append hprefix tailTrace_300550
  have hstable : (prefixWord ++ tailWord_300550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300550).length < 2 ^ (prefixWord ++ tailWord_300550).sum := by decide
  have hdescent : baseEnd_300550 < baseStart_300550 := by decide
  rcases family_descends (prefixWord ++ tailWord_300550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300564 : List Nat := [2, 4, 3, 1, 2, 2, 1, 1, 4]
def baseStart_300564 : Nat := 118140960795 + 300564 * 2 ^ 59
def prefixEnd_300564 : Nat := 4983230072969 + 3 ^ 40 * 300564 * 2
def baseEnd_300564 : Nat := 137185599500504245037989

theorem tailTrace_300564 : CollatzResearch.WordTrace tailWord_300564 prefixEnd_300564 137185599500504245037989 := by
  unfold tailWord_300564
  simp only [CollatzResearch.WordTrace]
  refine ⟨5481234841557717544770373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7308313122076956726360497 5481234841557717544770373)
  ·
    refine ⟨1027731532792072039644445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5481234841557717544770373 1027731532792072039644445)
    ·
      refine ⟨385399324797027014866667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1027731532792072039644445 385399324797027014866667)
      ·
        refine ⟨578098987195540522300001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385399324797027014866667 578098987195540522300001)
        ·
          refine ⟨433574240396655391725001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 578098987195540522300001 433574240396655391725001)
          ·
            refine ⟨325180680297491543793751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 433574240396655391725001 325180680297491543793751)
            ·
              refine ⟨487771020446237315690627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325180680297491543793751 487771020446237315690627)
              ·
                refine ⟨731656530669355973535941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 487771020446237315690627 731656530669355973535941)
                ·
                  refine ⟨137185599500504245037989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 731656530669355973535941 137185599500504245037989)
                  ·
                    rfl

theorem cell20_300564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_300564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300564 prefixEnd_300564 := by exact prefixLift 300564
  have htrace : WordTrace (prefixWord ++ tailWord_300564) baseStart_300564 baseEnd_300564 := by
    simpa [prefixWord, tailWord_300564, baseEnd_300564] using wordTrace_append hprefix tailTrace_300564
  have hstable : (prefixWord ++ tailWord_300564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300564).length < 2 ^ (prefixWord ++ tailWord_300564).sum := by decide
  have hdescent : baseEnd_300564 < baseStart_300564 := by decide
  rcases family_descends (prefixWord ++ tailWord_300564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300574 : List Nat := [4, 3, 3, 1, 1, 1, 1, 3, 3]
def baseStart_300574 : Nat := 118140960795 + 300574 * 2 ^ 59
def prefixEnd_300574 : Nat := 4983230072969 + 3 ^ 40 * 300574 * 2
def baseEnd_300574 : Nat := 137190163772988654704615

theorem tailTrace_300574 : CollatzResearch.WordTrace tailWord_300574 prefixEnd_300574 137190163772988654704615 := by
  unfold tailWord_300574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1370354301634900849675597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7308556275386137864936517 1370354301634900849675597)
  ·
    refine ⟨513882863113087818628349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1370354301634900849675597 513882863113087818628349)
    ·
      refine ⟨192706073667407931985631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 513882863113087818628349 192706073667407931985631)
      ·
        refine ⟨289059110501111897978447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192706073667407931985631 289059110501111897978447)
        ·
          refine ⟨433588665751667846967671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289059110501111897978447 433588665751667846967671)
          ·
            refine ⟨650382998627501770451507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433588665751667846967671 650382998627501770451507)
            ·
              refine ⟨975574497941252655677261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 650382998627501770451507 975574497941252655677261)
              ·
                refine ⟨365840436727969745878973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 975574497941252655677261 365840436727969745878973)
                ·
                  refine ⟨137190163772988654704615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 365840436727969745878973 137190163772988654704615)
                  ·
                    rfl

theorem cell20_300574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_300574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300574 prefixEnd_300574 := by exact prefixLift 300574
  have htrace : WordTrace (prefixWord ++ tailWord_300574) baseStart_300574 baseEnd_300574 := by
    simpa [prefixWord, tailWord_300574, baseEnd_300574] using wordTrace_append hprefix tailTrace_300574
  have hstable : (prefixWord ++ tailWord_300574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300574).length < 2 ^ (prefixWord ++ tailWord_300574).sum := by decide
  have hdescent : baseEnd_300574 < baseStart_300574 := by decide
  rcases family_descends (prefixWord ++ tailWord_300574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300620 : List Nat := [2, 2, 1, 3, 1, 3, 1, 4, 3]
def baseStart_300620 : Nat := 118140960795 + 300620 * 2 ^ 59
def prefixEnd_300620 : Nat := 4983230072969 + 3 ^ 40 * 300620 * 2
def baseEnd_300620 : Nat := 137211159426416939171093

theorem tailTrace_300620 : CollatzResearch.WordTrace tailWord_300620 prefixEnd_300620 137211159426416939171093 := by
  unfold tailWord_300620
  simp only [CollatzResearch.WordTrace]
  refine ⟨5482256085456278326789657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7309674780608371102386209 5482256085456278326789657)
  ·
    refine ⟨4111692064092208745092243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5482256085456278326789657 4111692064092208745092243)
    ·
      refine ⟨6167538096138313117638365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4111692064092208745092243 6167538096138313117638365)
      ·
        refine ⟨2312826786051867419114387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6167538096138313117638365 2312826786051867419114387)
        ·
          refine ⟨3469240179077801128671581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2312826786051867419114387 3469240179077801128671581)
          ·
            refine ⟨1300965067154175423251843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3469240179077801128671581 1300965067154175423251843)
            ·
              refine ⟨1951447600731263134877765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1300965067154175423251843 1951447600731263134877765)
              ·
                refine ⟨365896425137111837789581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1951447600731263134877765 365896425137111837789581)
                ·
                  refine ⟨137211159426416939171093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 365896425137111837789581 137211159426416939171093)
                  ·
                    rfl

theorem cell20_300620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_300620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300620 prefixEnd_300620 := by exact prefixLift 300620
  have htrace : WordTrace (prefixWord ++ tailWord_300620) baseStart_300620 baseEnd_300620 := by
    simpa [prefixWord, tailWord_300620, baseEnd_300620] using wordTrace_append hprefix tailTrace_300620
  have hstable : (prefixWord ++ tailWord_300620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300620).length < 2 ^ (prefixWord ++ tailWord_300620).sum := by decide
  have hdescent : baseEnd_300620 < baseStart_300620 := by decide
  rcases family_descends (prefixWord ++ tailWord_300620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300661 : List Nat := [1, 3, 4, 2, 1, 1, 1, 5, 2]
def baseStart_300661 : Nat := 118140960795 + 300661 * 2 ^ 59
def prefixEnd_300661 : Nat := 4983230072969 + 3 ^ 40 * 300661 * 2
def baseEnd_300661 : Nat := 137229872943603018804259

theorem tailTrace_300661 : CollatzResearch.WordTrace tailWord_300661 prefixEnd_300661 137229872943603018804259 := by
  unfold tailWord_300661
  simp only [CollatzResearch.WordTrace]
  refine ⟨10966007563764020655821837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7310671709176013770547891 10966007563764020655821837)
  ·
    refine ⟨4112252836411507745933189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10966007563764020655821837 4112252836411507745933189)
    ·
      refine ⟨771047406827157702362473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4112252836411507745933189 771047406827157702362473)
      ·
        refine ⟨578285555120368276771855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 771047406827157702362473 578285555120368276771855)
        ·
          refine ⟨867428332680552415157783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 578285555120368276771855 867428332680552415157783)
          ·
            refine ⟨1301142499020828622736675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 867428332680552415157783 1301142499020828622736675)
            ·
              refine ⟨1951713748531242934105013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1301142499020828622736675 1951713748531242934105013)
              ·
                refine ⟨182973163924804025072345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1951713748531242934105013 182973163924804025072345)
                ·
                  refine ⟨137229872943603018804259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182973163924804025072345 137229872943603018804259)
                  ·
                    rfl

theorem cell20_300661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 5, 2].length) (baseStart_300661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300661 prefixEnd_300661 := by exact prefixLift 300661
  have htrace : WordTrace (prefixWord ++ tailWord_300661) baseStart_300661 baseEnd_300661 := by
    simpa [prefixWord, tailWord_300661, baseEnd_300661] using wordTrace_append hprefix tailTrace_300661
  have hstable : (prefixWord ++ tailWord_300661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300661).length < 2 ^ (prefixWord ++ tailWord_300661).sum := by decide
  have hdescent : baseEnd_300661 < baseStart_300661 := by decide
  rcases family_descends (prefixWord ++ tailWord_300661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300682 : List Nat := [3, 1, 2, 3, 2, 2, 2, 1, 4]
def baseStart_300682 : Nat := 118140960795 + 300682 * 2 ^ 59
def prefixEnd_300682 : Nat := 4983230072969 + 3 ^ 40 * 300682 * 2
def baseEnd_300682 : Nat := 137239457915820279104173

theorem tailTrace_300682 : CollatzResearch.WordTrace tailWord_300682 prefixEnd_300682 137239457915820279104173 := by
  unfold tailWord_300682
  simp only [CollatzResearch.WordTrace]
  refine ⟨2741693374171985310584075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7311182331125294161557533 2741693374171985310584075)
  ·
    refine ⟨4112540061257977965876113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2741693374171985310584075 4112540061257977965876113)
    ·
      refine ⟨3084405045943483474407085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4112540061257977965876113 3084405045943483474407085)
      ·
        refine ⟨1156651892228806302902657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3084405045943483474407085 1156651892228806302902657)
        ·
          refine ⟨867488919171604727176993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1156651892228806302902657 867488919171604727176993)
          ·
            refine ⟨650616689378703545382745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 867488919171604727176993 650616689378703545382745)
            ·
              refine ⟨487962517034027659037059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 650616689378703545382745 487962517034027659037059)
              ·
                refine ⟨731943775551041488555589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 487962517034027659037059 731943775551041488555589)
                ·
                  refine ⟨137239457915820279104173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 731943775551041488555589 137239457915820279104173)
                  ·
                    rfl

theorem cell20_300682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_300682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300682 prefixEnd_300682 := by exact prefixLift 300682
  have htrace : WordTrace (prefixWord ++ tailWord_300682) baseStart_300682 baseEnd_300682 := by
    simpa [prefixWord, tailWord_300682, baseEnd_300682] using wordTrace_append hprefix tailTrace_300682
  have hstable : (prefixWord ++ tailWord_300682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300682).length < 2 ^ (prefixWord ++ tailWord_300682).sum := by decide
  have hdescent : baseEnd_300682 < baseStart_300682 := by decide
  rcases family_descends (prefixWord ++ tailWord_300682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300706 : List Nat := [3, 3, 1, 4, 1, 1, 1, 6]
def baseStart_300706 : Nat := 118140960795 + 300706 * 2 ^ 59
def prefixEnd_300706 : Nat := 4983230072969 + 3 ^ 40 * 300706 * 2
def baseEnd_300706 : Nat := 45750137389927620768025

theorem tailTrace_300706 : CollatzResearch.WordTrace tailWord_300706 prefixEnd_300706 45750137389927620768025 := by
  unfold tailWord_300706
  simp only [CollatzResearch.WordTrace]
  refine ⟨2741912212150248335302493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7311765899067328894139981 2741912212150248335302493)
  ·
    refine ⟨1028217079556343125738435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2741912212150248335302493 1028217079556343125738435)
    ·
      refine ⟨1542325619334514688607653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1028217079556343125738435 1542325619334514688607653)
      ·
        refine ⟨289186053625221504113935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1542325619334514688607653 289186053625221504113935)
        ·
          refine ⟨433779080437832256170903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289186053625221504113935 433779080437832256170903)
          ·
            refine ⟨650668620656748384256355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433779080437832256170903 650668620656748384256355)
            ·
              refine ⟨976002930985122576384533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 650668620656748384256355 976002930985122576384533)
              ·
                refine ⟨45750137389927620768025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 976002930985122576384533 45750137389927620768025)
                ·
                  rfl

theorem cell20_300706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_300706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300706 prefixEnd_300706 := by exact prefixLift 300706
  have htrace : WordTrace (prefixWord ++ tailWord_300706) baseStart_300706 baseEnd_300706 := by
    simpa [prefixWord, tailWord_300706, baseEnd_300706] using wordTrace_append hprefix tailTrace_300706
  have hstable : (prefixWord ++ tailWord_300706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300706).length < 2 ^ (prefixWord ++ tailWord_300706).sum := by decide
  have hdescent : baseEnd_300706 < baseStart_300706 := by decide
  rcases family_descends (prefixWord ++ tailWord_300706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300712 : List Nat := [2, 1, 7, 1, 1, 2, 1, 3, 2]
def baseStart_300712 : Nat := 118140960795 + 300712 * 2 ^ 59
def prefixEnd_300712 : Nat := 4983230072969 + 3 ^ 40 * 300712 * 2
def baseEnd_300712 : Nat := 137253150733273508104051

theorem tailTrace_300712 : CollatzResearch.WordTrace tailWord_300712 prefixEnd_300712 137253150733273508104051 := by
  unfold tailWord_300712
  simp only [CollatzResearch.WordTrace]
  refine ⟨5483933843289628182964195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7311911791052837577285593 5483933843289628182964195)
  ·
    refine ⟨8225900764934442274446293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5483933843289628182964195 8225900764934442274446293)
    ·
      refine ⟨192794549178150990807335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 8225900764934442274446293 192794549178150990807335)
      ·
        refine ⟨289191823767226486211003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192794549178150990807335 289191823767226486211003)
        ·
          refine ⟨433787735650839729316505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289191823767226486211003 433787735650839729316505)
          ·
            refine ⟨325340801738129796987379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 433787735650839729316505 325340801738129796987379)
            ·
              refine ⟨488011202607194695481069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325340801738129796987379 488011202607194695481069)
              ·
                refine ⟨183004200977698010805401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 488011202607194695481069 183004200977698010805401)
                ·
                  refine ⟨137253150733273508104051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183004200977698010805401 137253150733273508104051)
                  ·
                    rfl

theorem cell20_300712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 3, 2].length) (baseStart_300712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300712 prefixEnd_300712 := by exact prefixLift 300712
  have htrace : WordTrace (prefixWord ++ tailWord_300712) baseStart_300712 baseEnd_300712 := by
    simpa [prefixWord, tailWord_300712, baseEnd_300712] using wordTrace_append hprefix tailTrace_300712
  have hstable : (prefixWord ++ tailWord_300712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300712).length < 2 ^ (prefixWord ++ tailWord_300712).sum := by decide
  have hdescent : baseEnd_300712 < baseStart_300712 := by decide
  rcases family_descends (prefixWord ++ tailWord_300712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300720 : List Nat := [2, 1, 1, 1, 2, 1, 7, 3, 2]
def baseStart_300720 : Nat := 118140960795 + 300720 * 2 ^ 59
def prefixEnd_300720 : Nat := 4983230072969 + 3 ^ 40 * 300720 * 2
def baseEnd_300720 : Nat := 137256802151261035837351

theorem tailTrace_300720 : CollatzResearch.WordTrace tailWord_300720 prefixEnd_300720 137256802151261035837351 := by
  unfold tailWord_300720
  simp only [CollatzResearch.WordTrace]
  refine ⟨5484079735275136866109807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7312106313700182488146409 5484079735275136866109807)
  ·
    refine ⟨8226119602912705299164711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5484079735275136866109807 8226119602912705299164711)
    ·
      refine ⟨12339179404369057948747067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8226119602912705299164711 12339179404369057948747067)
      ·
        refine ⟨18508769106553586923120601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12339179404369057948747067 18508769106553586923120601)
        ·
          refine ⟨13881576829915190192340451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18508769106553586923120601 13881576829915190192340451)
          ·
            refine ⟨20822365244872785288510677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13881576829915190192340451 20822365244872785288510677)
            ·
              refine ⟨488024185426705905199469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 20822365244872785288510677 488024185426705905199469)
              ·
                refine ⟨183009069535014714449801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 488024185426705905199469 183009069535014714449801)
                ·
                  refine ⟨137256802151261035837351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183009069535014714449801 137256802151261035837351)
                  ·
                    rfl

theorem cell20_300720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 3, 2].length) (baseStart_300720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300720 prefixEnd_300720 := by exact prefixLift 300720
  have htrace : WordTrace (prefixWord ++ tailWord_300720) baseStart_300720 baseEnd_300720 := by
    simpa [prefixWord, tailWord_300720, baseEnd_300720] using wordTrace_append hprefix tailTrace_300720
  have hstable : (prefixWord ++ tailWord_300720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300720).length < 2 ^ (prefixWord ++ tailWord_300720).sum := by decide
  have hdescent : baseEnd_300720 < baseStart_300720 := by decide
  rcases family_descends (prefixWord ++ tailWord_300720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300734 : List Nat := [4, 2, 1, 1, 2, 2, 2, 1, 5]
def baseStart_300734 : Nat := 118140960795 + 300734 * 2 ^ 59
def prefixEnd_300734 : Nat := 4983230072969 + 3 ^ 40 * 300734 * 2
def baseEnd_300734 : Nat := 137263192132739209370627

theorem tailTrace_300734 : CollatzResearch.WordTrace tailWord_300734 prefixEnd_300734 137263192132739209370627 := by
  unfold tailWord_300734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1371083761562444265403657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7312446728333036082152837 1371083761562444265403657)
  ·
    refine ⟨1028312821171833199052743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1371083761562444265403657 1028312821171833199052743)
    ·
      refine ⟨1542469231757749798579115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1028312821171833199052743 1542469231757749798579115)
      ·
        refine ⟨2313703847636624697868673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1542469231757749798579115 2313703847636624697868673)
        ·
          refine ⟨1735277885727468523401505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2313703847636624697868673 1735277885727468523401505)
          ·
            refine ⟨1301458414295601392551129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1735277885727468523401505 1301458414295601392551129)
            ·
              refine ⟨976093810721701044413347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1301458414295601392551129 976093810721701044413347)
              ·
                refine ⟨1464140716082551566620021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 976093810721701044413347 1464140716082551566620021)
                ·
                  refine ⟨137263192132739209370627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1464140716082551566620021 137263192132739209370627)
                  ·
                    rfl

theorem cell20_300734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_300734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300734 prefixEnd_300734 := by exact prefixLift 300734
  have htrace : WordTrace (prefixWord ++ tailWord_300734) baseStart_300734 baseEnd_300734 := by
    simpa [prefixWord, tailWord_300734, baseEnd_300734] using wordTrace_append hprefix tailTrace_300734
  have hstable : (prefixWord ++ tailWord_300734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300734).length < 2 ^ (prefixWord ++ tailWord_300734).sum := by decide
  have hdescent : baseEnd_300734 < baseStart_300734 := by decide
  rcases family_descends (prefixWord ++ tailWord_300734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300788 : List Nat := [2, 6, 1, 1, 1, 3, 2, 2, 2]
def baseStart_300788 : Nat := 118140960795 + 300788 * 2 ^ 59
def prefixEnd_300788 : Nat := 4983230072969 + 3 ^ 40 * 300788 * 2
def baseEnd_300788 : Nat := 137287839204155021570407

theorem tailTrace_300788 : CollatzResearch.WordTrace tailWord_300788 prefixEnd_300788 137287839204155021570407 := by
  unfold tailWord_300788
  simp only [CollatzResearch.WordTrace]
  refine ⟨5485319817151960672847509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7313759756202614230463345 5485319817151960672847509)
  ·
    refine ⟨257124366428998156539727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5485319817151960672847509 257124366428998156539727)
    ·
      refine ⟨385686549643497234809591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257124366428998156539727 385686549643497234809591)
      ·
        refine ⟨578529824465245852214387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385686549643497234809591 578529824465245852214387)
        ·
          refine ⟨867794736697868778321581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 578529824465245852214387 867794736697868778321581)
          ·
            refine ⟨325423026261700791870593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 867794736697868778321581 325423026261700791870593)
            ·
              refine ⟨244067269696275593902945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325423026261700791870593 244067269696275593902945)
              ·
                refine ⟨183050452272206695427209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244067269696275593902945 183050452272206695427209)
                ·
                  refine ⟨137287839204155021570407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183050452272206695427209 137287839204155021570407)
                  ·
                    rfl

theorem cell20_300788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_300788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300788 prefixEnd_300788 := by exact prefixLift 300788
  have htrace : WordTrace (prefixWord ++ tailWord_300788) baseStart_300788 baseEnd_300788 := by
    simpa [prefixWord, tailWord_300788, baseEnd_300788] using wordTrace_append hprefix tailTrace_300788
  have hstable : (prefixWord ++ tailWord_300788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300788).length < 2 ^ (prefixWord ++ tailWord_300788).sum := by decide
  have hdescent : baseEnd_300788 < baseStart_300788 := by decide
  rcases family_descends (prefixWord ++ tailWord_300788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300796 : List Nat := [2, 2, 2, 1, 3, 1, 3, 4, 2]
def baseStart_300796 : Nat := 118140960795 + 300796 * 2 ^ 59
def prefixEnd_300796 : Nat := 4983230072969 + 3 ^ 40 * 300796 * 2
def baseEnd_300796 : Nat := 137291490622142549303707

theorem tailTrace_300796 : CollatzResearch.WordTrace tailWord_300796 prefixEnd_300796 137291490622142549303707 := by
  unfold tailWord_300796
  simp only [CollatzResearch.WordTrace]
  refine ⟨5485465709137469355993121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7313954278849959141324161 5485465709137469355993121)
  ·
    refine ⟨4114099281853102016994841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5485465709137469355993121 4114099281853102016994841)
    ·
      refine ⟨3085574461389826512746131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4114099281853102016994841 3085574461389826512746131)
      ·
        refine ⟨4628361692084739769119197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3085574461389826512746131 4628361692084739769119197)
        ·
          refine ⟨1735635634531777413419699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4628361692084739769119197 1735635634531777413419699)
          ·
            refine ⟨2603453451797666120129549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1735635634531777413419699 2603453451797666120129549)
            ·
              refine ⟨976295044424124795048581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2603453451797666120129549 976295044424124795048581)
              ·
                refine ⟨183055320829523399071609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 976295044424124795048581 183055320829523399071609)
                ·
                  refine ⟨137291490622142549303707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183055320829523399071609 137291490622142549303707)
                  ·
                    rfl

theorem cell20_300796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 4, 2].length) (baseStart_300796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300796 prefixEnd_300796 := by exact prefixLift 300796
  have htrace : WordTrace (prefixWord ++ tailWord_300796) baseStart_300796 baseEnd_300796 := by
    simpa [prefixWord, tailWord_300796, baseEnd_300796] using wordTrace_append hprefix tailTrace_300796
  have hstable : (prefixWord ++ tailWord_300796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300796).length < 2 ^ (prefixWord ++ tailWord_300796).sum := by decide
  have hdescent : baseEnd_300796 < baseStart_300796 := by decide
  rcases family_descends (prefixWord ++ tailWord_300796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300810 : List Nat := [3, 1, 2, 2, 1, 3, 2, 3, 3]
def baseStart_300810 : Nat := 118140960795 + 300810 * 2 ^ 59
def prefixEnd_300810 : Nat := 4983230072969 + 3 ^ 40 * 300810 * 2
def baseEnd_300810 : Nat := 137297880603620722836983

theorem tailTrace_300810 : CollatzResearch.WordTrace tailWord_300810 prefixEnd_300810 137297880603620722836983 := by
  unfold tailWord_300810
  simp only [CollatzResearch.WordTrace]
  refine ⟨2742860510056054775748971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7314294693482812735330589 2742860510056054775748971)
  ·
    refine ⟨4114290765084082163623457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2742860510056054775748971 4114290765084082163623457)
    ·
      refine ⟨3085718073813061622717593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4114290765084082163623457 3085718073813061622717593)
      ·
        refine ⟨2314288555359796217038195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3085718073813061622717593 2314288555359796217038195)
        ·
          refine ⟨3471432833039694325557293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2314288555359796217038195 3471432833039694325557293)
          ·
            refine ⟨1301787312389885372083985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3471432833039694325557293 1301787312389885372083985)
            ·
              refine ⟨976340484292414029062989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1301787312389885372083985 976340484292414029062989)
              ·
                refine ⟨366127681609655260898621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 976340484292414029062989 366127681609655260898621)
                ·
                  refine ⟨137297880603620722836983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 366127681609655260898621 137297880603620722836983)
                  ·
                    rfl

theorem cell20_300810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_300810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300810 prefixEnd_300810 := by exact prefixLift 300810
  have htrace : WordTrace (prefixWord ++ tailWord_300810) baseStart_300810 baseEnd_300810 := by
    simpa [prefixWord, tailWord_300810, baseEnd_300810] using wordTrace_append hprefix tailTrace_300810
  have hstable : (prefixWord ++ tailWord_300810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300810).length < 2 ^ (prefixWord ++ tailWord_300810).sum := by decide
  have hdescent : baseEnd_300810 < baseStart_300810 := by decide
  rcases family_descends (prefixWord ++ tailWord_300810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300831 : List Nat := [1, 1, 2, 4, 2, 1, 2, 2, 5]
def baseStart_300831 : Nat := 118140960795 + 300831 * 2 ^ 59
def prefixEnd_300831 : Nat := 4983230072969 + 3 ^ 40 * 300831 * 2
def baseEnd_300831 : Nat := 137307465575837983136897

theorem tailTrace_300831 : CollatzResearch.WordTrace tailWord_300831 prefixEnd_300831 137307465575837983136897 := by
  unfold tailWord_300831
  simp only [CollatzResearch.WordTrace]
  refine ⟨10972207973148139689510347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7314805315432093126340231 10972207973148139689510347)
  ·
    refine ⟨16458311959722209534265521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10972207973148139689510347 16458311959722209534265521)
    ·
      refine ⟨12343733969791657150699141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16458311959722209534265521 12343733969791657150699141)
      ·
        refine ⟨2314450119335935715756089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12343733969791657150699141 2314450119335935715756089)
        ·
          refine ⟨1735837589501951786817067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2314450119335935715756089 1735837589501951786817067)
          ·
            refine ⟨2603756384252927680225601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1735837589501951786817067 2603756384252927680225601)
            ·
              refine ⟨1952817288189695760169201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2603756384252927680225601 1952817288189695760169201)
              ·
                refine ⟨1464612966142271820126901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1952817288189695760169201 1464612966142271820126901)
                ·
                  refine ⟨137307465575837983136897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1464612966142271820126901 137307465575837983136897)
                  ·
                    rfl

theorem cell20_300831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 5].length) (baseStart_300831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300831 prefixEnd_300831 := by exact prefixLift 300831
  have htrace : WordTrace (prefixWord ++ tailWord_300831) baseStart_300831 baseEnd_300831 := by
    simpa [prefixWord, tailWord_300831, baseEnd_300831] using wordTrace_append hprefix tailTrace_300831
  have hstable : (prefixWord ++ tailWord_300831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300831).length < 2 ^ (prefixWord ++ tailWord_300831).sum := by decide
  have hdescent : baseEnd_300831 < baseStart_300831 := by decide
  rcases family_descends (prefixWord ++ tailWord_300831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300906 : List Nat := [3, 1, 3, 4, 2, 1, 1, 1, 4]
def baseStart_300906 : Nat := 118140960795 + 300906 * 2 ^ 59
def prefixEnd_300906 : Nat := 4983230072969 + 3 ^ 40 * 300906 * 2
def baseEnd_300906 : Nat := 137341697619471055636591

theorem tailTrace_300906 : CollatzResearch.WordTrace tailWord_300906 prefixEnd_300906 137341697619471055636591 := by
  unfold tailWord_300906
  simp only [CollatzResearch.WordTrace]
  refine ⟨2743735861969106874622643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7316628965250951665660381 2743735861969106874622643)
  ·
    refine ⟨4115603792953660311933965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2743735861969106874622643 4115603792953660311933965)
    ·
      refine ⟨1543351422357622616975237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4115603792953660311933965 1543351422357622616975237)
      ·
        refine ⟨289378391692054240682857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1543351422357622616975237 289378391692054240682857)
        ·
          refine ⟨217033793769040680512143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289378391692054240682857 217033793769040680512143)
          ·
            refine ⟨325550690653561020768215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217033793769040680512143 325550690653561020768215)
            ·
              refine ⟨488326035980341531152323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325550690653561020768215 488326035980341531152323)
              ·
                refine ⟨732489053970512296728485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 488326035980341531152323 732489053970512296728485)
                ·
                  refine ⟨137341697619471055636591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 732489053970512296728485 137341697619471055636591)
                  ·
                    rfl

theorem cell20_300906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 4].length) (baseStart_300906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300906 prefixEnd_300906 := by exact prefixLift 300906
  have htrace : WordTrace (prefixWord ++ tailWord_300906) baseStart_300906 baseEnd_300906 := by
    simpa [prefixWord, tailWord_300906, baseEnd_300906] using wordTrace_append hprefix tailTrace_300906
  have hstable : (prefixWord ++ tailWord_300906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300906).length < 2 ^ (prefixWord ++ tailWord_300906).sum := by decide
  have hdescent : baseEnd_300906 < baseStart_300906 := by decide
  rcases family_descends (prefixWord ++ tailWord_300906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300907 : List Nat := [1, 1, 1, 1, 2, 2, 3, 6, 3]
def baseStart_300907 : Nat := 118140960795 + 300907 * 2 ^ 59
def prefixEnd_300907 : Nat := 4983230072969 + 3 ^ 40 * 300907 * 2
def baseEnd_300907 : Nat := 137342154046719496603253

theorem tailTrace_300907 : CollatzResearch.WordTrace tailWord_300907 prefixEnd_300907 137342154046719496603253 := by
  unfold tailWord_300907
  simp only [CollatzResearch.WordTrace]
  refine ⟨10974979920872804669276975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7316653280581869779517983 10974979920872804669276975)
  ·
    refine ⟨16462469881309207003915463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10974979920872804669276975 16462469881309207003915463)
    ·
      refine ⟨24693704821963810505873195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16462469881309207003915463 24693704821963810505873195)
      ·
        refine ⟨37040557232945715758809793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24693704821963810505873195 37040557232945715758809793)
        ·
          refine ⟨27780417924709286819107345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37040557232945715758809793 27780417924709286819107345)
          ·
            refine ⟨20835313443531965114330509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27780417924709286819107345 20835313443531965114330509)
            ·
              refine ⟨7813242541324486917873941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20835313443531965114330509 7813242541324486917873941)
              ·
                refine ⟨366245744124585324275341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7813242541324486917873941 366245744124585324275341)
                ·
                  refine ⟨137342154046719496603253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 366245744124585324275341 137342154046719496603253)
                  ·
                    rfl

theorem cell20_300907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 3].length) (baseStart_300907 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300907 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300907 prefixEnd_300907 := by exact prefixLift 300907
  have htrace : WordTrace (prefixWord ++ tailWord_300907) baseStart_300907 baseEnd_300907 := by
    simpa [prefixWord, tailWord_300907, baseEnd_300907] using wordTrace_append hprefix tailTrace_300907
  have hstable : (prefixWord ++ tailWord_300907).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300907).length < 2 ^ (prefixWord ++ tailWord_300907).sum := by decide
  have hdescent : baseEnd_300907 < baseStart_300907 := by decide
  rcases family_descends (prefixWord ++ tailWord_300907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300910 : List Nat := [4, 1, 2, 3, 1, 1, 3, 1, 4]
def baseStart_300910 : Nat := 118140960795 + 300910 * 2 ^ 59
def prefixEnd_300910 : Nat := 4983230072969 + 3 ^ 40 * 300910 * 2
def baseEnd_300910 : Nat := 137343523328464819503241

theorem tailTrace_300910 : CollatzResearch.WordTrace tailWord_300910 prefixEnd_300910 137343523328464819503241 := by
  unfold tailWord_300910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1371886167482742022704523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7316726226574624121090789 1371886167482742022704523)
  ·
    refine ⟨2057829251224113034056785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1371886167482742022704523 2057829251224113034056785)
    ·
      refine ⟨1543371938418084775542589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2057829251224113034056785 1543371938418084775542589)
      ·
        refine ⟨578764476906781790828471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1543371938418084775542589 578764476906781790828471)
        ·
          refine ⟨868146715360172686242707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 578764476906781790828471 868146715360172686242707)
          ·
            refine ⟨1302220073040259029364061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 868146715360172686242707 1302220073040259029364061)
            ·
              refine ⟨488332527390097136011523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1302220073040259029364061 488332527390097136011523)
              ·
                refine ⟨732498791085145704017285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 488332527390097136011523 732498791085145704017285)
                ·
                  refine ⟨137343523328464819503241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 732498791085145704017285 137343523328464819503241)
                  ·
                    rfl

theorem cell20_300910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_300910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300910 prefixEnd_300910 := by exact prefixLift 300910
  have htrace : WordTrace (prefixWord ++ tailWord_300910) baseStart_300910 baseEnd_300910 := by
    simpa [prefixWord, tailWord_300910, baseEnd_300910] using wordTrace_append hprefix tailTrace_300910
  have hstable : (prefixWord ++ tailWord_300910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300910).length < 2 ^ (prefixWord ++ tailWord_300910).sum := by decide
  have hdescent : baseEnd_300910 < baseStart_300910 := by decide
  rcases family_descends (prefixWord ++ tailWord_300910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300959 : List Nat := [1, 1, 2, 5, 11]
def baseStart_300959 : Nat := 118140960795 + 300959 * 2 ^ 59
def prefixEnd_300959 : Nat := 4983230072969 + 3 ^ 40 * 300959 * 2
def baseEnd_300959 : Nat := 1695875163748622553947

theorem tailTrace_300959 : CollatzResearch.WordTrace tailWord_300959 prefixEnd_300959 1695875163748622553947 := by
  unfold tailWord_300959
  simp only [CollatzResearch.WordTrace]
  refine ⟨10976876516684417550169931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7317917677789611700113287 10976876516684417550169931)
  ·
    refine ⟨16465314775026626325254897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10976876516684417550169931 16465314775026626325254897)
    ·
      refine ⟨12348986081269969743941173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16465314775026626325254897 12348986081269969743941173)
      ·
        refine ⟨1157717445119059663494485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12348986081269969743941173 1157717445119059663494485)
        ·
          refine ⟨1695875163748622553947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1157717445119059663494485 1695875163748622553947)
          ·
            rfl

theorem cell20_300959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 11].length) (baseStart_300959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300959 prefixEnd_300959 := by exact prefixLift 300959
  have htrace : WordTrace (prefixWord ++ tailWord_300959) baseStart_300959 baseEnd_300959 := by
    simpa [prefixWord, tailWord_300959, baseEnd_300959] using wordTrace_append hprefix tailTrace_300959
  have hstable : (prefixWord ++ tailWord_300959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300959).length < 2 ^ (prefixWord ++ tailWord_300959).sum := by decide
  have hdescent : baseEnd_300959 < baseStart_300959 := by decide
  rcases family_descends (prefixWord ++ tailWord_300959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300961 : List Nat := [1, 2, 3, 4, 3, 1, 2, 2, 2]
def baseStart_300961 : Nat := 118140960795 + 300961 * 2 ^ 59
def prefixEnd_300961 : Nat := 4983230072969 + 3 ^ 40 * 300961 * 2
def baseEnd_300961 : Nat := 137366801118135308803033

theorem tailTrace_300961 : CollatzResearch.WordTrace tailWord_300961 prefixEnd_300961 137366801118135308803033 := by
  unfold tailWord_300961
  simp only [CollatzResearch.WordTrace]
  refine ⟨10976949462677171891742737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7317966308451447927828491 10976949462677171891742737)
  ·
    refine ⟨8232712097007878918807053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10976949462677171891742737 8232712097007878918807053)
    ·
      refine ⟨3087267036377954594552645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8232712097007878918807053 3087267036377954594552645)
      ·
        refine ⟨578862569320866486478621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3087267036377954594552645 578862569320866486478621)
        ·
          refine ⟨217073463495324932429483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 578862569320866486478621 217073463495324932429483)
          ·
            refine ⟨325610195242987398644225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217073463495324932429483 325610195242987398644225)
            ·
              refine ⟨244207646432240548983169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325610195242987398644225 244207646432240548983169)
              ·
                refine ⟨183155734824180411737377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244207646432240548983169 183155734824180411737377)
                ·
                  refine ⟨137366801118135308803033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183155734824180411737377 137366801118135308803033)
                  ·
                    rfl

theorem cell20_300961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 2, 2].length) (baseStart_300961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_300961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_300961 prefixEnd_300961 := by exact prefixLift 300961
  have htrace : WordTrace (prefixWord ++ tailWord_300961) baseStart_300961 baseEnd_300961 := by
    simpa [prefixWord, tailWord_300961, baseEnd_300961] using wordTrace_append hprefix tailTrace_300961
  have hstable : (prefixWord ++ tailWord_300961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300961).length < 2 ^ (prefixWord ++ tailWord_300961).sum := by decide
  have hdescent : baseEnd_300961 < baseStart_300961 := by decide
  rcases family_descends (prefixWord ++ tailWord_300961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301017 : List Nat := [1, 2, 1, 2, 6, 2, 1, 2, 3]
def baseStart_301017 : Nat := 118140960795 + 301017 * 2 ^ 59
def prefixEnd_301017 : Nat := 4983230072969 + 3 ^ 40 * 301017 * 2
def baseEnd_301017 : Nat := 137392361044048002936137

theorem tailTrace_301017 : CollatzResearch.WordTrace tailWord_301017 prefixEnd_301017 137392361044048002936137 := by
  unfold tailWord_301017
  simp only [CollatzResearch.WordTrace]
  refine ⟨10978991950474293455781305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7319327966982862303854203 10978991950474293455781305)
  ·
    refine ⟨8234243962855720091835979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10978991950474293455781305 8234243962855720091835979)
    ·
      refine ⟨12351365944283580137753969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8234243962855720091835979 12351365944283580137753969)
      ·
        refine ⟨9263524458212685103315477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12351365944283580137753969 9263524458212685103315477)
        ·
          refine ⟨434227708978719614217913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9263524458212685103315477 434227708978719614217913)
          ·
            refine ⟨325670781734039710663435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 434227708978719614217913 325670781734039710663435)
            ·
              refine ⟨488506172601059565995153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325670781734039710663435 488506172601059565995153)
              ·
                refine ⟨366379629450794674496365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 488506172601059565995153 366379629450794674496365)
                ·
                  refine ⟨137392361044048002936137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 366379629450794674496365 137392361044048002936137)
                  ·
                    rfl

theorem cell20_301017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 3].length) (baseStart_301017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301017 prefixEnd_301017 := by exact prefixLift 301017
  have htrace : WordTrace (prefixWord ++ tailWord_301017) baseStart_301017 baseEnd_301017 := by
    simpa [prefixWord, tailWord_301017, baseEnd_301017] using wordTrace_append hprefix tailTrace_301017
  have hstable : (prefixWord ++ tailWord_301017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301017).length < 2 ^ (prefixWord ++ tailWord_301017).sum := by decide
  have hdescent : baseEnd_301017 < baseStart_301017 := by decide
  rcases family_descends (prefixWord ++ tailWord_301017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301020 : List Nat := [2, 2, 6, 1, 1, 1, 2, 1, 4]
def baseStart_301020 : Nat := 118140960795 + 301020 * 2 ^ 59
def prefixEnd_301020 : Nat := 4983230072969 + 3 ^ 40 * 301020 * 2
def baseEnd_301020 : Nat := 137393730325793325836125

theorem tailTrace_301020 : CollatzResearch.WordTrace tailWord_301020 prefixEnd_301020 137393730325793325836125 := by
  unfold tailWord_301020
  simp only [CollatzResearch.WordTrace]
  refine ⟨5489550684731712484070257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7319400912975616645427009 5489550684731712484070257)
  ·
    refine ⟨4117163013548784363052693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5489550684731712484070257 4117163013548784363052693)
    ·
      refine ⟨192992016260099267018095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4117163013548784363052693 192992016260099267018095)
      ·
        refine ⟨289488024390148900527143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192992016260099267018095 289488024390148900527143)
        ·
          refine ⟨434232036585223350790715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289488024390148900527143 434232036585223350790715)
          ·
            refine ⟨651348054877835026186073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434232036585223350790715 651348054877835026186073)
            ·
              refine ⟨488511041158376269639555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 651348054877835026186073 488511041158376269639555)
              ·
                refine ⟨732766561737564404459333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 488511041158376269639555 732766561737564404459333)
                ·
                  refine ⟨137393730325793325836125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 732766561737564404459333 137393730325793325836125)
                  ·
                    rfl

theorem cell20_301020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 4].length) (baseStart_301020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301020 prefixEnd_301020 := by exact prefixLift 301020
  have htrace : WordTrace (prefixWord ++ tailWord_301020) baseStart_301020 baseEnd_301020 := by
    simpa [prefixWord, tailWord_301020, baseEnd_301020] using wordTrace_append hprefix tailTrace_301020
  have hstable : (prefixWord ++ tailWord_301020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301020).length < 2 ^ (prefixWord ++ tailWord_301020).sum := by decide
  have hdescent : baseEnd_301020 < baseStart_301020 := by decide
  rcases family_descends (prefixWord ++ tailWord_301020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301079 : List Nat := [1, 1, 3, 5, 3, 1, 1, 1, 4]
def baseStart_301079 : Nat := 118140960795 + 301079 * 2 ^ 59
def prefixEnd_301079 : Nat := 4983230072969 + 3 ^ 40 * 301079 * 2
def baseEnd_301079 : Nat := 137420659533451342869217

theorem tailTrace_301079 : CollatzResearch.WordTrace tailWord_301079 prefixEnd_301079 137420659533451342869217 := by
  unfold tailWord_301079
  simp only [CollatzResearch.WordTrace]
  refine ⟨10981253276249678044538291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7320835517499785363025527 10981253276249678044538291)
  ·
    refine ⟨16471879914374517066807437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10981253276249678044538291 16471879914374517066807437)
    ·
      refine ⟨6176954967890443900052789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16471879914374517066807437 6176954967890443900052789)
      ·
        refine ⟨579089528239729115629949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6176954967890443900052789 579089528239729115629949)
        ·
          refine ⟨217158573089898418361231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 579089528239729115629949 217158573089898418361231)
          ·
            refine ⟨325737859634847627541847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217158573089898418361231 325737859634847627541847)
            ·
              refine ⟨488606789452271441312771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325737859634847627541847 488606789452271441312771)
              ·
                refine ⟨732910184178407161969157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 488606789452271441312771 732910184178407161969157)
                ·
                  refine ⟨137420659533451342869217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 732910184178407161969157 137420659533451342869217)
                  ·
                    rfl

theorem cell20_301079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 4].length) (baseStart_301079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301079 prefixEnd_301079 := by exact prefixLift 301079
  have htrace : WordTrace (prefixWord ++ tailWord_301079) baseStart_301079 baseEnd_301079 := by
    simpa [prefixWord, tailWord_301079, baseEnd_301079] using wordTrace_append hprefix tailTrace_301079
  have hstable : (prefixWord ++ tailWord_301079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301079).length < 2 ^ (prefixWord ++ tailWord_301079).sum := by decide
  have hdescent : baseEnd_301079 < baseStart_301079 := by decide
  rcases family_descends (prefixWord ++ tailWord_301079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301090 : List Nat := [3, 3, 1, 1, 1, 2, 4, 5]
def baseStart_301090 : Nat := 118140960795 + 301090 * 2 ^ 59
def prefixEnd_301090 : Nat := 4983230072969 + 3 ^ 40 * 301090 * 2
def baseEnd_301090 : Nat := 45808560077728064500835

theorem tailTrace_301090 : CollatzResearch.WordTrace tailWord_301090 prefixEnd_301090 45808560077728064500835 := by
  unfold tailWord_301090
  simp only [CollatzResearch.WordTrace]
  refine ⟨2745413619802456730797181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7321102986139884615459149 2745413619802456730797181)
  ·
    refine ⟨1029530107425921274048943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2745413619802456730797181 1029530107425921274048943)
    ·
      refine ⟨1544295161138881911073415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1029530107425921274048943 1544295161138881911073415)
      ·
        refine ⟨2316442741708322866610123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1544295161138881911073415 2316442741708322866610123)
        ·
          refine ⟨3474664112562484299915185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2316442741708322866610123 3474664112562484299915185)
          ·
            refine ⟨2605998084421863224936389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3474664112562484299915185 2605998084421863224936389)
            ·
              refine ⟨488624640829099354675573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2605998084421863224936389 488624640829099354675573)
              ·
                refine ⟨45808560077728064500835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 488624640829099354675573 45808560077728064500835)
                ·
                  rfl

theorem cell20_301090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_301090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301090 prefixEnd_301090 := by exact prefixLift 301090
  have htrace : WordTrace (prefixWord ++ tailWord_301090) baseStart_301090 baseEnd_301090 := by
    simpa [prefixWord, tailWord_301090, baseEnd_301090] using wordTrace_append hprefix tailTrace_301090
  have hstable : (prefixWord ++ tailWord_301090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301090).length < 2 ^ (prefixWord ++ tailWord_301090).sum := by decide
  have hdescent : baseEnd_301090 < baseStart_301090 := by decide
  rcases family_descends (prefixWord ++ tailWord_301090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301093 : List Nat := [1, 3, 1, 2, 2, 5, 2, 1, 3]
def baseStart_301093 : Nat := 118140960795 + 301093 * 2 ^ 59
def prefixEnd_301093 : Nat := 4983230072969 + 3 ^ 40 * 301093 * 2
def baseEnd_301093 : Nat := 137427049514929516402493

theorem tailTrace_301093 : CollatzResearch.WordTrace tailWord_301093 prefixEnd_301093 137427049514929516402493 := by
  unfold tailWord_301093
  simp only [CollatzResearch.WordTrace]
  refine ⟨10981763898198958435547933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7321175932132638957031955 10981763898198958435547933)
  ·
    refine ⟨4118161461824609413330475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10981763898198958435547933 4118161461824609413330475)
    ·
      refine ⟨6177242192736914119995713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4118161461824609413330475 6177242192736914119995713)
      ·
        refine ⟨4632931644552685589996785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6177242192736914119995713 4632931644552685589996785)
        ·
          refine ⟨3474698733414514192497589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4632931644552685589996785 3474698733414514192497589)
          ·
            refine ⟨325753006257610705546649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3474698733414514192497589 325753006257610705546649)
            ·
              refine ⟨244314754693208029159987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325753006257610705546649 244314754693208029159987)
              ·
                refine ⟨366472132039812043739981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244314754693208029159987 366472132039812043739981)
                ·
                  refine ⟨137427049514929516402493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 366472132039812043739981 137427049514929516402493)
                  ·
                    rfl

theorem cell20_301093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_301093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301093 prefixEnd_301093 := by exact prefixLift 301093
  have htrace : WordTrace (prefixWord ++ tailWord_301093) baseStart_301093 baseEnd_301093 := by
    simpa [prefixWord, tailWord_301093, baseEnd_301093] using wordTrace_append hprefix tailTrace_301093
  have hstable : (prefixWord ++ tailWord_301093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301093).length < 2 ^ (prefixWord ++ tailWord_301093).sum := by decide
  have hdescent : baseEnd_301093 < baseStart_301093 := by decide
  rcases family_descends (prefixWord ++ tailWord_301093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301111 : List Nat := [1, 1, 3, 1, 2, 2, 4, 6]
def baseStart_301111 : Nat := 118140960795 + 301111 * 2 ^ 59
def prefixEnd_301111 : Nat := 4983230072969 + 3 ^ 40 * 301111 * 2
def baseEnd_301111 : Nat := 45811755068467151267473

theorem tailTrace_301111 : CollatzResearch.WordTrace tailWord_301111 prefixEnd_301111 45811755068467151267473 := by
  unfold tailWord_301111
  simp only [CollatzResearch.WordTrace]
  refine ⟨10982420412133747509703187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7321613608089165006468791 10982420412133747509703187)
  ·
    refine ⟨16473630618200621264554781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10982420412133747509703187 16473630618200621264554781)
    ·
      refine ⟨6177611481825232974208043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16473630618200621264554781 6177611481825232974208043)
      ·
        refine ⟨9266417222737849461312065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6177611481825232974208043 9266417222737849461312065)
        ·
          refine ⟨6949812917053387095984049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9266417222737849461312065 6949812917053387095984049)
          ·
            refine ⟨5212359687790040321988037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6949812917053387095984049 5212359687790040321988037)
            ·
              refine ⟨977317441460632560372757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5212359687790040321988037 977317441460632560372757)
              ·
                refine ⟨45811755068467151267473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 977317441460632560372757 45811755068467151267473)
                ·
                  rfl

theorem cell20_301111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 6].length) (baseStart_301111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301111 prefixEnd_301111 := by exact prefixLift 301111
  have htrace : WordTrace (prefixWord ++ tailWord_301111) baseStart_301111 baseEnd_301111 := by
    simpa [prefixWord, tailWord_301111, baseEnd_301111] using wordTrace_append hprefix tailTrace_301111
  have hstable : (prefixWord ++ tailWord_301111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301111).length < 2 ^ (prefixWord ++ tailWord_301111).sum := by decide
  have hdescent : baseEnd_301111 < baseStart_301111 := by decide
  rcases family_descends (prefixWord ++ tailWord_301111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301187 : List Nat := [1, 1, 1, 3, 3, 4, 7]
def baseStart_301187 : Nat := 118140960795 + 301187 * 2 ^ 59
def prefixEnd_301187 : Nat := 4983230072969 + 3 ^ 40 * 301187 * 2
def baseEnd_301187 : Nat := 15274439297364774140975

theorem tailTrace_301187 : CollatzResearch.WordTrace tailWord_301187 prefixEnd_301187 15274439297364774140975 := by
  unfold tailWord_301187
  simp only [CollatzResearch.WordTrace]
  refine ⟨10985192359858412489469815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7323461573238941659646543 10985192359858412489469815)
  ·
    refine ⟨16477788539787618734204723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10985192359858412489469815 16477788539787618734204723)
    ·
      refine ⟨24716682809681428101307085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16477788539787618734204723 24716682809681428101307085)
      ·
        refine ⟨9268756053630535537990157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24716682809681428101307085 9268756053630535537990157)
        ·
          refine ⟨3475783520111450826746309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9268756053630535537990157 3475783520111450826746309)
          ·
            refine ⟨651709410020897030014933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3475783520111450826746309 651709410020897030014933)
            ·
              refine ⟨15274439297364774140975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 651709410020897030014933 15274439297364774140975)
              ·
                rfl

theorem cell20_301187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 7].length) (baseStart_301187 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301187 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301187 prefixEnd_301187 := by exact prefixLift 301187
  have htrace : WordTrace (prefixWord ++ tailWord_301187) baseStart_301187 baseEnd_301187 := by
    simpa [prefixWord, tailWord_301187, baseEnd_301187] using wordTrace_append hprefix tailTrace_301187
  have hstable : (prefixWord ++ tailWord_301187).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301187).length < 2 ^ (prefixWord ++ tailWord_301187).sum := by decide
  have hdescent : baseEnd_301187 < baseStart_301187 := by decide
  rcases family_descends (prefixWord ++ tailWord_301187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301207 : List Nat := [1, 1, 3, 3, 4, 1, 3, 1, 3]
def baseStart_301207 : Nat := 118140960795 + 301207 * 2 ^ 59
def prefixEnd_301207 : Nat := 4983230072969 + 3 ^ 40 * 301207 * 2
def baseEnd_301207 : Nat := 137479082221251786602027

theorem tailTrace_301207 : CollatzResearch.WordTrace tailWord_301207 prefixEnd_301207 137479082221251786602027 := by
  unfold tailWord_301207
  simp only [CollatzResearch.WordTrace]
  refine ⟨10985921819785955905197875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7323947879857303936798583 10985921819785955905197875)
  ·
    refine ⟨16478882729678933857796813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10985921819785955905197875 16478882729678933857796813)
    ·
      refine ⟨6179581023629600196673805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16478882729678933857796813 6179581023629600196673805)
      ·
        refine ⟨2317342883861100073752677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6179581023629600196673805 2317342883861100073752677)
        ·
          refine ⟨434501790723956263828627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2317342883861100073752677 434501790723956263828627)
          ·
            refine ⟨651752686085934395742941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434501790723956263828627 651752686085934395742941)
            ·
              refine ⟨244407257282225398403603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 651752686085934395742941 244407257282225398403603)
              ·
                refine ⟨366610885923338097605405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244407257282225398403603 366610885923338097605405)
                ·
                  refine ⟨137479082221251786602027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 366610885923338097605405 137479082221251786602027)
                  ·
                    rfl

theorem cell20_301207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 3].length) (baseStart_301207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301207 prefixEnd_301207 := by exact prefixLift 301207
  have htrace : WordTrace (prefixWord ++ tailWord_301207) baseStart_301207 baseEnd_301207 := by
    simpa [prefixWord, tailWord_301207, baseEnd_301207] using wordTrace_append hprefix tailTrace_301207
  have hstable : (prefixWord ++ tailWord_301207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301207).length < 2 ^ (prefixWord ++ tailWord_301207).sum := by decide
  have hdescent : baseEnd_301207 < baseStart_301207 := by decide
  rcases family_descends (prefixWord ++ tailWord_301207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301252 : List Nat := [2, 3, 3, 1, 2, 3, 1, 1, 4]
def baseStart_301252 : Nat := 118140960795 + 301252 * 2 ^ 59
def prefixEnd_301252 : Nat := 4983230072969 + 3 ^ 40 * 301252 * 2
def baseEnd_301252 : Nat := 137499621447431630101843

theorem tailTrace_301252 : CollatzResearch.WordTrace tailWord_301252 prefixEnd_301252 137499621447431630101843 := by
  unfold tailWord_301252
  simp only [CollatzResearch.WordTrace]
  refine ⟨5493781552311464295293005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7325042069748619060390673 5493781552311464295293005)
  ·
    refine ⟨2060168082116799110734877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5493781552311464295293005 2060168082116799110734877)
    ·
      refine ⟨772563030793799666525579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2060168082116799110734877 772563030793799666525579)
      ·
        refine ⟨1158844546190699499788369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 772563030793799666525579 1158844546190699499788369)
        ·
          refine ⟨869133409643024624841277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1158844546190699499788369 869133409643024624841277)
          ·
            refine ⟨325925028616134234315479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 869133409643024624841277 325925028616134234315479)
            ·
              refine ⟨488887542924201351473219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325925028616134234315479 488887542924201351473219)
              ·
                refine ⟨733331314386302027209829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 488887542924201351473219 733331314386302027209829)
                ·
                  refine ⟨137499621447431630101843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 733331314386302027209829 137499621447431630101843)
                  ·
                    rfl

theorem cell20_301252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_301252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301252 prefixEnd_301252 := by exact prefixLift 301252
  have htrace : WordTrace (prefixWord ++ tailWord_301252) baseStart_301252 baseEnd_301252 := by
    simpa [prefixWord, tailWord_301252, baseEnd_301252] using wordTrace_append hprefix tailTrace_301252
  have hstable : (prefixWord ++ tailWord_301252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301252).length < 2 ^ (prefixWord ++ tailWord_301252).sum := by decide
  have hdescent : baseEnd_301252 < baseStart_301252 := by decide
  rcases family_descends (prefixWord ++ tailWord_301252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301263 : List Nat := [1, 1, 2, 1, 1, 3, 6, 5]
def baseStart_301263 : Nat := 118140960795 + 301263 * 2 ^ 59
def prefixEnd_301263 : Nat := 4983230072969 + 3 ^ 40 * 301263 * 2
def baseEnd_301263 : Nat := 45834880715721493578377

theorem tailTrace_301263 : CollatzResearch.WordTrace tailWord_301263 prefixEnd_301263 45834880715721493578377 := by
  unfold tailWord_301263
  simp only [CollatzResearch.WordTrace]
  refine ⟨10987964307583077469236443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7325309538388718312824295 10987964307583077469236443)
  ·
    refine ⟨16481946461374616203854665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10987964307583077469236443 16481946461374616203854665)
    ·
      refine ⟨12361459846030962152890999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16481946461374616203854665 12361459846030962152890999)
      ·
        refine ⟨18542189769046443229336499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12361459846030962152890999 18542189769046443229336499)
        ·
          refine ⟨27813284653569664844004749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18542189769046443229336499 27813284653569664844004749)
          ·
            refine ⟨10429981745088624316501781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27813284653569664844004749 10429981745088624316501781)
            ·
              refine ⟨488905394301029264836021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10429981745088624316501781 488905394301029264836021)
              ·
                refine ⟨45834880715721493578377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 488905394301029264836021 45834880715721493578377)
                ·
                  rfl

theorem cell20_301263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 5].length) (baseStart_301263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301263 prefixEnd_301263 := by exact prefixLift 301263
  have htrace : WordTrace (prefixWord ++ tailWord_301263) baseStart_301263 baseEnd_301263 := by
    simpa [prefixWord, tailWord_301263, baseEnd_301263] using wordTrace_append hprefix tailTrace_301263
  have hstable : (prefixWord ++ tailWord_301263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301263).length < 2 ^ (prefixWord ++ tailWord_301263).sum := by decide
  have hdescent : baseEnd_301263 < baseStart_301263 := by decide
  rcases family_descends (prefixWord ++ tailWord_301263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301266 : List Nat := [3, 2, 2, 2, 1, 3, 1, 3, 3]
def baseStart_301266 : Nat := 118140960795 + 301266 * 2 ^ 59
def prefixEnd_301266 : Nat := 4983230072969 + 3 ^ 40 * 301266 * 2
def baseEnd_301266 : Nat := 137506011428909803635119

theorem tailTrace_301266 : CollatzResearch.WordTrace tailWord_301266 prefixEnd_301266 137506011428909803635119 := by
  unfold tailWord_301266
  simp only [CollatzResearch.WordTrace]
  refine ⟨2747018431643052245398913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7325382484381472654397101 2747018431643052245398913)
  ·
    refine ⟨2060263823732289184049185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2747018431643052245398913 2060263823732289184049185)
    ·
      refine ⟨1545197867799216888036889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2060263823732289184049185 1545197867799216888036889)
      ·
        refine ⟨1158898400849412666027667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1545197867799216888036889 1158898400849412666027667)
        ·
          refine ⟨1738347601274118999041501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1158898400849412666027667 1738347601274118999041501)
          ·
            refine ⟨651880350477794624640563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1738347601274118999041501 651880350477794624640563)
            ·
              refine ⟨977820525716691936960845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 651880350477794624640563 977820525716691936960845)
              ·
                refine ⟨366682697143759476360317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 977820525716691936960845 366682697143759476360317)
                ·
                  refine ⟨137506011428909803635119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 366682697143759476360317 137506011428909803635119)
                  ·
                    rfl

theorem cell20_301266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_301266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301266 prefixEnd_301266 := by exact prefixLift 301266
  have htrace : WordTrace (prefixWord ++ tailWord_301266) baseStart_301266 baseEnd_301266 := by
    simpa [prefixWord, tailWord_301266, baseEnd_301266] using wordTrace_append hprefix tailTrace_301266
  have hstable : (prefixWord ++ tailWord_301266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301266).length < 2 ^ (prefixWord ++ tailWord_301266).sum := by decide
  have hdescent : baseEnd_301266 < baseStart_301266 := by decide
  rcases family_descends (prefixWord ++ tailWord_301266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301311 : List Nat := [1, 1, 2, 2, 1, 4, 3, 4, 2]
def baseStart_301311 : Nat := 118140960795 + 301311 * 2 ^ 59
def prefixEnd_301311 : Nat := 4983230072969 + 3 ^ 40 * 301311 * 2
def baseEnd_301311 : Nat := 137526550655089647134935

theorem tailTrace_301311 : CollatzResearch.WordTrace tailWord_301311 prefixEnd_301311 137526550655089647134935 := by
  unfold tailWord_301311
  simp only [CollatzResearch.WordTrace]
  refine ⟨10989715011409181666983787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7326476674272787777989191 10989715011409181666983787)
  ·
    refine ⟨16484572517113772500475681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10989715011409181666983787 16484572517113772500475681)
    ·
      refine ⟨12363429387835329375356761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16484572517113772500475681 12363429387835329375356761)
      ·
        refine ⟨9272572040876497031517571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12363429387835329375356761 9272572040876497031517571)
        ·
          refine ⟨13908858061314745547276357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9272572040876497031517571 13908858061314745547276357)
          ·
            refine ⟨2607910886496514790114317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13908858061314745547276357 2607910886496514790114317)
            ·
              refine ⟨977966582436193046292869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2607910886496514790114317 977966582436193046292869)
              ·
                refine ⟨183368734206786196179913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 977966582436193046292869 183368734206786196179913)
                ·
                  refine ⟨137526550655089647134935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183368734206786196179913 137526550655089647134935)
                  ·
                    rfl

theorem cell20_301311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 4, 2].length) (baseStart_301311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301311 prefixEnd_301311 := by exact prefixLift 301311
  have htrace : WordTrace (prefixWord ++ tailWord_301311) baseStart_301311 baseEnd_301311 := by
    simpa [prefixWord, tailWord_301311, baseEnd_301311] using wordTrace_append hprefix tailTrace_301311
  have hstable : (prefixWord ++ tailWord_301311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301311).length < 2 ^ (prefixWord ++ tailWord_301311).sum := by decide
  have hdescent : baseEnd_301311 < baseStart_301311 := by decide
  rcases family_descends (prefixWord ++ tailWord_301311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301370 : List Nat := [3, 1, 1, 1, 4, 2, 1, 3, 4]
def baseStart_301370 : Nat := 118140960795 + 301370 * 2 ^ 59
def prefixEnd_301370 : Nat := 4983230072969 + 3 ^ 40 * 301370 * 2
def baseEnd_301370 : Nat := 137553479862747664168027

theorem tailTrace_301370 : CollatzResearch.WordTrace tailWord_301370 prefixEnd_301370 137553479862747664168027 := by
  unfold tailWord_301370
  simp only [CollatzResearch.WordTrace]
  refine ⟨2747966729548858685845391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7327911278796956495587709 2747966729548858685845391)
  ·
    refine ⟨4121950094323288028768087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2747966729548858685845391 4121950094323288028768087)
    ·
      refine ⟨6182925141484932043152131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4121950094323288028768087 6182925141484932043152131)
      ·
        refine ⟨9274387712227398064728197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6182925141484932043152131 9274387712227398064728197)
        ·
          refine ⟨1738947696042637137136537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9274387712227398064728197 1738947696042637137136537)
          ·
            refine ⟨1304210772031977852852403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1738947696042637137136537 1304210772031977852852403)
            ·
              refine ⟨1956316158047966779278605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1304210772031977852852403 1956316158047966779278605)
              ·
                refine ⟨733618559267987542229477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1956316158047966779278605 733618559267987542229477)
                ·
                  refine ⟨137553479862747664168027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 733618559267987542229477 137553479862747664168027)
                  ·
                    rfl

theorem cell20_301370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_301370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301370 prefixEnd_301370 := by exact prefixLift 301370
  have htrace : WordTrace (prefixWord ++ tailWord_301370) baseStart_301370 baseEnd_301370 := by
    simpa [prefixWord, tailWord_301370, baseEnd_301370] using wordTrace_append hprefix tailTrace_301370
  have hstable : (prefixWord ++ tailWord_301370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301370).length < 2 ^ (prefixWord ++ tailWord_301370).sum := by decide
  have hdescent : baseEnd_301370 < baseStart_301370 := by decide
  rcases family_descends (prefixWord ++ tailWord_301370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301391 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 6]
def baseStart_301391 : Nat := 118140960795 + 301391 * 2 ^ 59
def prefixEnd_301391 : Nat := 4983230072969 + 3 ^ 40 * 301391 * 2
def baseEnd_301391 : Nat := 137563064834964924467941

theorem tailTrace_301391 : CollatzResearch.WordTrace tailWord_301391 prefixEnd_301391 137563064834964924467941 := by
  unfold tailWord_301391
  simp only [CollatzResearch.WordTrace]
  refine ⟨10992632851119355329896027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7328421900746236886597351 10992632851119355329896027)
  ·
    refine ⟨16488949276679032994844041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10992632851119355329896027 16488949276679032994844041)
    ·
      refine ⟨12366711957509274746133031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16488949276679032994844041 12366711957509274746133031)
      ·
        refine ⟨18550067936263912119199547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12366711957509274746133031 18550067936263912119199547)
        ·
          refine ⟨27825101904395868178799321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18550067936263912119199547 27825101904395868178799321)
          ·
            refine ⟨20868826428296901134099491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27825101904395868178799321 20868826428296901134099491)
            ·
              refine ⟨31303239642445351701149237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20868826428296901134099491 31303239642445351701149237)
              ·
                refine ⟨2934678716479251721982741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31303239642445351701149237 2934678716479251721982741)
                ·
                  refine ⟨137563064834964924467941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2934678716479251721982741 137563064834964924467941)
                  ·
                    rfl

theorem cell20_301391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 6].length) (baseStart_301391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301391 prefixEnd_301391 := by exact prefixLift 301391
  have htrace : WordTrace (prefixWord ++ tailWord_301391) baseStart_301391 baseEnd_301391 := by
    simpa [prefixWord, tailWord_301391, baseEnd_301391] using wordTrace_append hprefix tailTrace_301391
  have hstable : (prefixWord ++ tailWord_301391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301391).length < 2 ^ (prefixWord ++ tailWord_301391).sum := by decide
  have hdescent : baseEnd_301391 < baseStart_301391 := by decide
  rcases family_descends (prefixWord ++ tailWord_301391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301394 : List Nat := [3, 2, 2, 1, 1, 1, 6, 4]
def baseStart_301394 : Nat := 118140960795 + 301394 * 2 ^ 59
def prefixEnd_301394 : Nat := 4983230072969 + 3 ^ 40 * 301394 * 2
def baseEnd_301394 : Nat := 45854811372236749122643

theorem tailTrace_301394 : CollatzResearch.WordTrace tailWord_301394 prefixEnd_301394 45854811372236749122643 := by
  unfold tailWord_301394
  simp only [CollatzResearch.WordTrace]
  refine ⟨2748185567527121710563809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7328494846738991228170157 2748185567527121710563809)
  ·
    refine ⟨2061139175645341282922857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2748185567527121710563809 2061139175645341282922857)
    ·
      refine ⟨1545854381734005962192143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2061139175645341282922857 1545854381734005962192143)
      ·
        refine ⟨2318781572601008943288215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1545854381734005962192143 2318781572601008943288215)
        ·
          refine ⟨3478172358901513414932323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2318781572601008943288215 3478172358901513414932323)
          ·
            refine ⟨5217258538352270122398485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3478172358901513414932323 5217258538352270122398485)
            ·
              refine ⟨244558993985262661987429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5217258538352270122398485 244558993985262661987429)
              ·
                refine ⟨45854811372236749122643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 244558993985262661987429 45854811372236749122643)
                ·
                  rfl

theorem cell20_301394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_301394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301394 prefixEnd_301394 := by exact prefixLift 301394
  have htrace : WordTrace (prefixWord ++ tailWord_301394) baseStart_301394 baseEnd_301394 := by
    simpa [prefixWord, tailWord_301394, baseEnd_301394] using wordTrace_append hprefix tailTrace_301394
  have hstable : (prefixWord ++ tailWord_301394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301394).length < 2 ^ (prefixWord ++ tailWord_301394).sum := by decide
  have hdescent : baseEnd_301394 < baseStart_301394 := by decide
  rcases family_descends (prefixWord ++ tailWord_301394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301415 : List Nat := [1, 1, 5, 1, 3, 1, 8]
def baseStart_301415 : Nat := 118140960795 + 301415 * 2 ^ 59
def prefixEnd_301415 : Nat := 4983230072969 + 3 ^ 40 * 301415 * 2
def baseEnd_301415 : Nat := 15286002120991945296427

theorem tailTrace_301415 : CollatzResearch.WordTrace tailWord_301415 prefixEnd_301415 15286002120991945296427 := by
  unfold tailWord_301415
  simp only [CollatzResearch.WordTrace]
  refine ⟨10993508203032407428769699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7329005468688271619179799 10993508203032407428769699)
  ·
    refine ⟨16490262304548611143154549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10993508203032407428769699 16490262304548611143154549)
    ·
      refine ⟨1545962091051432294670739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16490262304548611143154549 1545962091051432294670739)
      ·
        refine ⟨2318943136577148442006109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1545962091051432294670739 2318943136577148442006109)
        ·
          refine ⟨869603676216430665752291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2318943136577148442006109 869603676216430665752291)
          ·
            refine ⟨1304405514324645998628437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 869603676216430665752291 1304405514324645998628437)
            ·
              refine ⟨15286002120991945296427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1304405514324645998628437 15286002120991945296427)
              ·
                rfl

theorem cell20_301415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 8].length) (baseStart_301415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301415 prefixEnd_301415 := by exact prefixLift 301415
  have htrace : WordTrace (prefixWord ++ tailWord_301415) baseStart_301415 baseEnd_301415 := by
    simpa [prefixWord, tailWord_301415, baseEnd_301415] using wordTrace_append hprefix tailTrace_301415
  have hstable : (prefixWord ++ tailWord_301415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301415).length < 2 ^ (prefixWord ++ tailWord_301415).sum := by decide
  have hdescent : baseEnd_301415 < baseStart_301415 := by decide
  rcases family_descends (prefixWord ++ tailWord_301415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301470 : List Nat := [4, 3, 1, 2, 1, 9]
def baseStart_301470 : Nat := 118140960795 + 301470 * 2 ^ 59
def prefixEnd_301470 : Nat := 4983230072969 + 3 ^ 40 * 301470 * 2
def baseEnd_301470 : Nat := 5096263799540435586455

theorem tailTrace_301470 : CollatzResearch.WordTrace tailWord_301470 prefixEnd_301470 5096263799540435586455 := by
  unfold tailWord_301470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1374439277229143977752733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7330342811888767881347909 1374439277229143977752733)
  ·
    refine ⟨515414728960928991657275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1374439277229143977752733 515414728960928991657275)
    ·
      refine ⟨773122093441393487485913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 515414728960928991657275 773122093441393487485913)
      ·
        refine ⟨579841570081045115614435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 773122093441393487485913 579841570081045115614435)
        ·
          refine ⟨869762355121567673421653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 579841570081045115614435 869762355121567673421653)
          ·
            refine ⟨5096263799540435586455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 869762355121567673421653 5096263799540435586455)
            ·
              rfl

theorem cell20_301470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 9].length) (baseStart_301470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301470 prefixEnd_301470 := by exact prefixLift 301470
  have htrace : WordTrace (prefixWord ++ tailWord_301470) baseStart_301470 baseEnd_301470 := by
    simpa [prefixWord, tailWord_301470, baseEnd_301470] using wordTrace_append hprefix tailTrace_301470
  have hstable : (prefixWord ++ tailWord_301470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301470).length < 2 ^ (prefixWord ++ tailWord_301470).sum := by decide
  have hdescent : baseEnd_301470 < baseStart_301470 := by decide
  rcases family_descends (prefixWord ++ tailWord_301470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301473 : List Nat := [1, 2, 3, 5, 1, 1, 2, 2, 3]
def baseStart_301473 : Nat := 118140960795 + 301473 * 2 ^ 59
def prefixEnd_301473 : Nat := 4983230072969 + 3 ^ 40 * 301473 * 2
def baseEnd_301473 : Nat := 137600491869337083734273

theorem tailTrace_301473 : CollatzResearch.WordTrace tailWord_301473 prefixEnd_301473 137600491869337083734273 := by
  unfold tailWord_301473
  simp only [CollatzResearch.WordTrace]
  refine ⟨10995623636822283334381073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7330415757881522222920715 10995623636822283334381073)
  ·
    refine ⟨8246717727616712500785805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10995623636822283334381073 8246717727616712500785805)
    ·
      refine ⟨3092519147856267187794677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8246717727616712500785805 3092519147856267187794677)
      ·
        refine ⟨289923670111525048855751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3092519147856267187794677 289923670111525048855751)
        ·
          refine ⟨434885505167287573283627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289923670111525048855751 434885505167287573283627)
          ·
            refine ⟨652328257750931359925441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434885505167287573283627 652328257750931359925441)
            ·
              refine ⟨489246193313198519944081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 652328257750931359925441 489246193313198519944081)
              ·
                refine ⟨366934644984898889958061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 489246193313198519944081 366934644984898889958061)
                ·
                  refine ⟨137600491869337083734273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 366934644984898889958061 137600491869337083734273)
                  ·
                    rfl

theorem cell20_301473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 3].length) (baseStart_301473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301473 prefixEnd_301473 := by exact prefixLift 301473
  have htrace : WordTrace (prefixWord ++ tailWord_301473) baseStart_301473 baseEnd_301473 := by
    simpa [prefixWord, tailWord_301473, baseEnd_301473] using wordTrace_append hprefix tailTrace_301473
  have hstable : (prefixWord ++ tailWord_301473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301473).length < 2 ^ (prefixWord ++ tailWord_301473).sum := by decide
  have hdescent : baseEnd_301473 < baseStart_301473 := by decide
  rcases family_descends (prefixWord ++ tailWord_301473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301477 : List Nat := [1, 3, 1, 2, 1, 1, 6, 2, 3]
def baseStart_301477 : Nat := 118140960795 + 301477 * 2 ^ 59
def prefixEnd_301477 : Nat := 4983230072969 + 3 ^ 40 * 301477 * 2
def baseEnd_301477 : Nat := 137602317578330847600923

theorem tailTrace_301477 : CollatzResearch.WordTrace tailWord_301477 prefixEnd_301477 137602317578330847600923 := by
  unfold tailWord_301477
  simp only [CollatzResearch.WordTrace]
  refine ⟨10995769528807792017526685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7330513019205194678351123 10995769528807792017526685)
  ·
    refine ⟨4123413573302922006572507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10995769528807792017526685 4123413573302922006572507)
    ·
      refine ⟨6185120359954383009858761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4123413573302922006572507 6185120359954383009858761)
      ·
        refine ⟨4638840269965787257394071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6185120359954383009858761 4638840269965787257394071)
        ·
          refine ⟨6958260404948680886091107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4638840269965787257394071 6958260404948680886091107)
          ·
            refine ⟨10437390607423021329136661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6958260404948680886091107 10437390607423021329136661)
            ·
              refine ⟨489252684722954124803281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10437390607423021329136661 489252684722954124803281)
              ·
                refine ⟨366939513542215593602461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 489252684722954124803281 366939513542215593602461)
                ·
                  refine ⟨137602317578330847600923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 366939513542215593602461 137602317578330847600923)
                  ·
                    rfl

theorem cell20_301477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_301477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301477 prefixEnd_301477 := by exact prefixLift 301477
  have htrace : WordTrace (prefixWord ++ tailWord_301477) baseStart_301477 baseEnd_301477 := by
    simpa [prefixWord, tailWord_301477, baseEnd_301477] using wordTrace_append hprefix tailTrace_301477
  have hstable : (prefixWord ++ tailWord_301477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301477).length < 2 ^ (prefixWord ++ tailWord_301477).sum := by decide
  have hdescent : baseEnd_301477 < baseStart_301477 := by decide
  rcases family_descends (prefixWord ++ tailWord_301477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301536 : List Nat := [2, 1, 1, 3, 1, 1, 5, 1, 5]
def baseStart_301536 : Nat := 118140960795 + 301536 * 2 ^ 59
def prefixEnd_301536 : Nat := 4983230072969 + 3 ^ 40 * 301536 * 2
def baseEnd_301536 : Nat := 137629246785988864634015

theorem tailTrace_301536 : CollatzResearch.WordTrace tailWord_301536 prefixEnd_301536 137629246785988864634015 := by
  unfold tailWord_301536
  simp only [CollatzResearch.WordTrace]
  refine ⟨5498960717797022546962231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7331947623729363395949641 5498960717797022546962231)
  ·
    refine ⟨8248441076695533820443347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5498960717797022546962231 8248441076695533820443347)
    ·
      refine ⟨12372661615043300730665021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8248441076695533820443347 12372661615043300730665021)
      ·
        refine ⟨4639748105641237773999383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12372661615043300730665021 4639748105641237773999383)
        ·
          refine ⟨6959622158461856660999075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4639748105641237773999383 6959622158461856660999075)
          ·
            refine ⟨10439433237692784991498613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6959622158461856660999075 10439433237692784991498613)
            ·
              refine ⟨978696866033698592952995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10439433237692784991498613 978696866033698592952995)
              ·
                refine ⟨1468045299050547889429493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 978696866033698592952995 1468045299050547889429493)
                ·
                  refine ⟨137629246785988864634015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1468045299050547889429493 137629246785988864634015)
                  ·
                    rfl

theorem cell20_301536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_301536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301536 prefixEnd_301536 := by exact prefixLift 301536
  have htrace : WordTrace (prefixWord ++ tailWord_301536) baseStart_301536 baseEnd_301536 := by
    simpa [prefixWord, tailWord_301536, baseEnd_301536] using wordTrace_append hprefix tailTrace_301536
  have hstable : (prefixWord ++ tailWord_301536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301536).length < 2 ^ (prefixWord ++ tailWord_301536).sum := by decide
  have hdescent : baseEnd_301536 < baseStart_301536 := by decide
  rcases family_descends (prefixWord ++ tailWord_301536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301539 : List Nat := [1, 1, 1, 6, 3, 1, 2, 1, 4]
def baseStart_301539 : Nat := 118140960795 + 301539 * 2 ^ 59
def prefixEnd_301539 : Nat := 4983230072969 + 3 ^ 40 * 301539 * 2
def baseEnd_301539 : Nat := 137630616067734187534003

theorem tailTrace_301539 : CollatzResearch.WordTrace tailWord_301539 prefixEnd_301539 137630616067734187534003 := by
  unfold tailWord_301539
  simp only [CollatzResearch.WordTrace]
  refine ⟨10998030854583176606283671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7332020569722117737522447 10998030854583176606283671)
  ·
    refine ⟨16497046281874764909425507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10998030854583176606283671 16497046281874764909425507)
    ·
      refine ⟨24745569422812147364138261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16497046281874764909425507 24745569422812147364138261)
      ·
        refine ⟨1159948566694319407693981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24745569422812147364138261 1159948566694319407693981)
        ·
          refine ⟨434980712510369777885243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1159948566694319407693981 434980712510369777885243)
          ·
            refine ⟨652471068765554666827865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434980712510369777885243 652471068765554666827865)
            ·
              refine ⟨489353301574166000120899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 652471068765554666827865 489353301574166000120899)
              ·
                refine ⟨734029952361249000181349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 489353301574166000120899 734029952361249000181349)
                ·
                  refine ⟨137630616067734187534003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 734029952361249000181349 137630616067734187534003)
                  ·
                    rfl

theorem cell20_301539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 4].length) (baseStart_301539 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301539 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301539 prefixEnd_301539 := by exact prefixLift 301539
  have htrace : WordTrace (prefixWord ++ tailWord_301539) baseStart_301539 baseEnd_301539 := by
    simpa [prefixWord, tailWord_301539, baseEnd_301539] using wordTrace_append hprefix tailTrace_301539
  have hstable : (prefixWord ++ tailWord_301539).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301539).length < 2 ^ (prefixWord ++ tailWord_301539).sum := by decide
  have hdescent : baseEnd_301539 < baseStart_301539 := by decide
  rcases family_descends (prefixWord ++ tailWord_301539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301549 : List Nat := [1, 5, 1, 3, 1, 2, 3, 1, 3]
def baseStart_301549 : Nat := 118140960795 + 301549 * 2 ^ 59
def prefixEnd_301549 : Nat := 4983230072969 + 3 ^ 40 * 301549 * 2
def baseEnd_301549 : Nat := 137635180340218597200629

theorem tailTrace_301549 : CollatzResearch.WordTrace tailWord_301549 prefixEnd_301549 137635180340218597200629 := by
  unfold tailWord_301549
  simp only [CollatzResearch.WordTrace]
  refine ⟨10998395584546948314147701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7332263723031298876098467 10998395584546948314147701)
  ·
    refine ⟨1031099586051276404451347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10998395584546948314147701 1031099586051276404451347)
    ·
      refine ⟨1546649379076914606677021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1031099586051276404451347 1546649379076914606677021)
      ·
        refine ⟨579993517153842977503883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1546649379076914606677021 579993517153842977503883)
        ·
          refine ⟨869990275730764466255825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 579993517153842977503883 869990275730764466255825)
          ·
            refine ⟨652492706798073349691869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 869990275730764466255825 652492706798073349691869)
            ·
              refine ⟨244684765049277506134451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 652492706798073349691869 244684765049277506134451)
              ·
                refine ⟨367027147573916259201677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244684765049277506134451 367027147573916259201677)
                ·
                  refine ⟨137635180340218597200629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 367027147573916259201677 137635180340218597200629)
                  ·
                    rfl

theorem cell20_301549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_301549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301549 prefixEnd_301549 := by exact prefixLift 301549
  have htrace : WordTrace (prefixWord ++ tailWord_301549) baseStart_301549 baseEnd_301549 := by
    simpa [prefixWord, tailWord_301549, baseEnd_301549] using wordTrace_append hprefix tailTrace_301549
  have hstable : (prefixWord ++ tailWord_301549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301549).length < 2 ^ (prefixWord ++ tailWord_301549).sum := by decide
  have hdescent : baseEnd_301549 < baseStart_301549 := by decide
  rcases family_descends (prefixWord ++ tailWord_301549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301604 : List Nat := [2, 3, 1, 5, 1, 2, 2, 1, 3]
def baseStart_301604 : Nat := 118140960795 + 301604 * 2 ^ 59
def prefixEnd_301604 : Nat := 4983230072969 + 3 ^ 40 * 301604 * 2
def baseEnd_301604 : Nat := 137660283838882850367071

theorem tailTrace_301604 : CollatzResearch.WordTrace tailWord_301604 prefixEnd_301604 137660283838882850367071 := by
  unfold tailWord_301604
  simp only [CollatzResearch.WordTrace]
  refine ⟨5500200799673846353699933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7333601066231795138266577 5500200799673846353699933)
  ·
    refine ⟨2062575299877692382637475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5500200799673846353699933 2062575299877692382637475)
    ·
      refine ⟨3093862949816538573956213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2062575299877692382637475 3093862949816538573956213)
      ·
        refine ⟨290049651545300491308395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3093862949816538573956213 290049651545300491308395)
        ·
          refine ⟨435074477317950736962593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290049651545300491308395 435074477317950736962593)
          ·
            refine ⟨326305857988463052721945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 435074477317950736962593 326305857988463052721945)
            ·
              refine ⟨244729393491347289541459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326305857988463052721945 244729393491347289541459)
              ·
                refine ⟨367094090237020934312189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244729393491347289541459 367094090237020934312189)
                ·
                  refine ⟨137660283838882850367071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 367094090237020934312189 137660283838882850367071)
                  ·
                    rfl

theorem cell20_301604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_301604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301604 prefixEnd_301604 := by exact prefixLift 301604
  have htrace : WordTrace (prefixWord ++ tailWord_301604) baseStart_301604 baseEnd_301604 := by
    simpa [prefixWord, tailWord_301604, baseEnd_301604] using wordTrace_append hprefix tailTrace_301604
  have hstable : (prefixWord ++ tailWord_301604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301604).length < 2 ^ (prefixWord ++ tailWord_301604).sum := by decide
  have hdescent : baseEnd_301604 < baseStart_301604 := by decide
  rcases family_descends (prefixWord ++ tailWord_301604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301608 : List Nat := [2, 1, 5, 2, 1, 2, 1, 3, 3]
def baseStart_301608 : Nat := 118140960795 + 301608 * 2 ^ 59
def prefixEnd_301608 : Nat := 4983230072969 + 3 ^ 40 * 301608 * 2
def baseEnd_301608 : Nat := 137662109547876614233721

theorem tailTrace_301608 : CollatzResearch.WordTrace tailWord_301608 prefixEnd_301608 137662109547876614233721 := by
  unfold tailWord_301608
  simp only [CollatzResearch.WordTrace]
  refine ⟨5500273745666600695272739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7333698327555467593696985 5500273745666600695272739)
  ·
    refine ⟨8250410618499901042909109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5500273745666600695272739 8250410618499901042909109)
    ·
      refine ⟨773475995484365722772729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8250410618499901042909109 773475995484365722772729)
      ·
        refine ⟨580106996613274292079547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 773475995484365722772729 580106996613274292079547)
        ·
          refine ⟨870160494919911438119321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580106996613274292079547 870160494919911438119321)
          ·
            refine ⟨652620371189933578589491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 870160494919911438119321 652620371189933578589491)
            ·
              refine ⟨978930556784900367884237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 652620371189933578589491 978930556784900367884237)
              ·
                refine ⟨367098958794337637956589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 978930556784900367884237 367098958794337637956589)
                ·
                  refine ⟨137662109547876614233721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 367098958794337637956589 137662109547876614233721)
                  ·
                    rfl

theorem cell20_301608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 3].length) (baseStart_301608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301608 prefixEnd_301608 := by exact prefixLift 301608
  have htrace : WordTrace (prefixWord ++ tailWord_301608) baseStart_301608 baseEnd_301608 := by
    simpa [prefixWord, tailWord_301608, baseEnd_301608] using wordTrace_append hprefix tailTrace_301608
  have hstable : (prefixWord ++ tailWord_301608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301608).length < 2 ^ (prefixWord ++ tailWord_301608).sum := by decide
  have hdescent : baseEnd_301608 < baseStart_301608 := by decide
  rcases family_descends (prefixWord ++ tailWord_301608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301619 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 6]
def baseStart_301619 : Nat := 118140960795 + 301619 * 2 ^ 59
def prefixEnd_301619 : Nat := 4983230072969 + 3 ^ 40 * 301619 * 2
def baseEnd_301619 : Nat := 137667130247609464867009

theorem tailTrace_301619 : CollatzResearch.WordTrace tailWord_301619 prefixEnd_301619 137667130247609464867009 := by
  unfold tailWord_301619
  simp only [CollatzResearch.WordTrace]
  refine ⟨11000948694293350269195911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7333965796195566846130607 11000948694293350269195911)
  ·
    refine ⟨16501423041440025403793867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11000948694293350269195911 16501423041440025403793867)
    ·
      refine ⟨24752134562160038105690801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16501423041440025403793867 24752134562160038105690801)
      ·
        refine ⟨18564100921620028579268101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24752134562160038105690801 18564100921620028579268101)
        ·
          refine ⟨3480768922803755358612769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18564100921620028579268101 3480768922803755358612769)
          ·
            refine ⟨2610576692102816518959577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3480768922803755358612769 2610576692102816518959577)
            ·
              refine ⟨1957932519077112389219683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2610576692102816518959577 1957932519077112389219683)
              ·
                refine ⟨2936898778615668583829525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1957932519077112389219683 2936898778615668583829525)
                ·
                  refine ⟨137667130247609464867009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2936898778615668583829525 137667130247609464867009)
                  ·
                    rfl

theorem cell20_301619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 6].length) (baseStart_301619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301619 prefixEnd_301619 := by exact prefixLift 301619
  have htrace : WordTrace (prefixWord ++ tailWord_301619) baseStart_301619 baseEnd_301619 := by
    simpa [prefixWord, tailWord_301619, baseEnd_301619] using wordTrace_append hprefix tailTrace_301619
  have hstable : (prefixWord ++ tailWord_301619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301619).length < 2 ^ (prefixWord ++ tailWord_301619).sum := by decide
  have hdescent : baseEnd_301619 < baseStart_301619 := by decide
  rcases family_descends (prefixWord ++ tailWord_301619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301622 : List Nat := [5, 1, 2, 1, 2, 1, 2, 6]
def baseStart_301622 : Nat := 118140960795 + 301622 * 2 ^ 59
def prefixEnd_301622 : Nat := 4983230072969 + 3 ^ 40 * 301622 * 2
def baseEnd_301622 : Nat := 45889499843118262588999

theorem tailTrace_301622 : CollatzResearch.WordTrace tailWord_301622 prefixEnd_301622 45889499843118262588999 := by
  unfold tailWord_301622
  simp only [CollatzResearch.WordTrace]
  refine ⟨687566132080155111347195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7334038742188321187703413 687566132080155111347195)
  ·
    refine ⟨1031349198120232667020793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 687566132080155111347195 1031349198120232667020793)
    ·
      refine ⟨773511898590174500265595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1031349198120232667020793 773511898590174500265595)
      ·
        refine ⟨1160267847885261750398393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 773511898590174500265595 1160267847885261750398393)
        ·
          refine ⟨870200885913946312798795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1160267847885261750398393 870200885913946312798795)
          ·
            refine ⟨1305301328870919469198193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 870200885913946312798795 1305301328870919469198193)
            ·
              refine ⟨978975996653189601898645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1305301328870919469198193 978975996653189601898645)
              ·
                refine ⟨45889499843118262588999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 978975996653189601898645 45889499843118262588999)
                ·
                  rfl

theorem cell20_301622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_301622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301622 prefixEnd_301622 := by exact prefixLift 301622
  have htrace : WordTrace (prefixWord ++ tailWord_301622) baseStart_301622 baseEnd_301622 := by
    simpa [prefixWord, tailWord_301622, baseEnd_301622] using wordTrace_append hprefix tailTrace_301622
  have hstable : (prefixWord ++ tailWord_301622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301622).length < 2 ^ (prefixWord ++ tailWord_301622).sum := by decide
  have hdescent : baseEnd_301622 < baseStart_301622 := by decide
  rcases family_descends (prefixWord ++ tailWord_301622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301674 : List Nat := [3, 1, 3, 2, 1, 1, 3, 2, 4]
def baseStart_301674 : Nat := 118140960795 + 301674 * 2 ^ 59
def prefixEnd_301674 : Nat := 4983230072969 + 3 ^ 40 * 301674 * 2
def baseEnd_301674 : Nat := 137692233746273718033451

theorem tailTrace_301674 : CollatzResearch.WordTrace tailWord_301674 prefixEnd_301674 137692233746273718033451 := by
  unfold tailWord_301674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2750738677273523665612019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7335303139396063108298717 2750738677273523665612019)
  ·
    refine ⟨4126108015910285498418029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2750738677273523665612019 4126108015910285498418029)
    ·
      refine ⟨1547290505966357061906761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4126108015910285498418029 1547290505966357061906761)
      ·
        refine ⟨1160467879474767796430071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1547290505966357061906761 1160467879474767796430071)
        ·
          refine ⟨1740701819212151694645107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1160467879474767796430071 1740701819212151694645107)
          ·
            refine ⟨2611052728818227541967661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1740701819212151694645107 2611052728818227541967661)
            ·
              refine ⟨979144773306835328237873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2611052728818227541967661 979144773306835328237873)
              ·
                refine ⟨734358579980126496178405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 979144773306835328237873 734358579980126496178405)
                ·
                  refine ⟨137692233746273718033451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 734358579980126496178405 137692233746273718033451)
                  ·
                    rfl

theorem cell20_301674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_301674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301674 prefixEnd_301674 := by exact prefixLift 301674
  have htrace : WordTrace (prefixWord ++ tailWord_301674) baseStart_301674 baseEnd_301674 := by
    simpa [prefixWord, tailWord_301674, baseEnd_301674] using wordTrace_append hprefix tailTrace_301674
  have hstable : (prefixWord ++ tailWord_301674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301674).length < 2 ^ (prefixWord ++ tailWord_301674).sum := by decide
  have hdescent : baseEnd_301674 < baseStart_301674 := by decide
  rcases family_descends (prefixWord ++ tailWord_301674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301757 : List Nat := [1, 4, 1, 2, 1, 5, 6]
def baseStart_301757 : Nat := 118140960795 + 301757 * 2 ^ 59
def prefixEnd_301757 : Nat := 4983230072969 + 3 ^ 40 * 301757 * 2
def baseEnd_301757 : Nat := 15303346356432702029605

theorem tailTrace_301757 : CollatzResearch.WordTrace tailWord_301757 prefixEnd_301757 15303346356432702029605 := by
  unfold tailWord_301757
  simp only [CollatzResearch.WordTrace]
  refine ⟨11005981967793399837719525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7337321311862266558479683 11005981967793399837719525)
  ·
    refine ⟨2063621618961262469572411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11005981967793399837719525 2063621618961262469572411)
    ·
      refine ⟨3095432428441893704358617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2063621618961262469572411 3095432428441893704358617)
      ·
        refine ⟨2321574321331420278268963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3095432428441893704358617 2321574321331420278268963)
        ·
          refine ⟨3482361481997130417403445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2321574321331420278268963 3482361481997130417403445)
          ·
            refine ⟨326471388937230976631573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3482361481997130417403445 326471388937230976631573)
            ·
              refine ⟨15303346356432702029605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 326471388937230976631573 15303346356432702029605)
              ·
                rfl

theorem cell20_301757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 6].length) (baseStart_301757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301757 prefixEnd_301757 := by exact prefixLift 301757
  have htrace : WordTrace (prefixWord ++ tailWord_301757) baseStart_301757 baseEnd_301757 := by
    simpa [prefixWord, tailWord_301757, baseEnd_301757] using wordTrace_append hprefix tailTrace_301757
  have hstable : (prefixWord ++ tailWord_301757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301757).length < 2 ^ (prefixWord ++ tailWord_301757).sum := by decide
  have hdescent : baseEnd_301757 < baseStart_301757 := by decide
  rcases family_descends (prefixWord ++ tailWord_301757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301773 : List Nat := [1, 6, 2, 1, 3, 1, 2, 1, 3]
def baseStart_301773 : Nat := 118140960795 + 301773 * 2 ^ 59
def prefixEnd_301773 : Nat := 4983230072969 + 3 ^ 40 * 301773 * 2
def baseEnd_301773 : Nat := 137737420043869373733047

theorem tailTrace_301773 : CollatzResearch.WordTrace tailWord_301773 prefixEnd_301773 137737420043869373733047 := by
  unfold tailWord_301773
  simp only [CollatzResearch.WordTrace]
  refine ⟨11006565535735434570301973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7337710357156956380201315 11006565535735434570301973)
  ·
    refine ⟨515932759487598495482905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11006565535735434570301973 515932759487598495482905)
    ·
      refine ⟨386949569615698871612179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 515932759487598495482905 386949569615698871612179)
      ·
        refine ⟨580424354423548307418269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386949569615698871612179 580424354423548307418269)
        ·
          refine ⟨217659132908830615281851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 580424354423548307418269 217659132908830615281851)
          ·
            refine ⟨326488699363245922922777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217659132908830615281851 326488699363245922922777)
            ·
              refine ⟨244866524522434442192083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326488699363245922922777 244866524522434442192083)
              ·
                refine ⟨367299786783651663288125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244866524522434442192083 367299786783651663288125)
                ·
                  refine ⟨137737420043869373733047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 367299786783651663288125 137737420043869373733047)
                  ·
                    rfl

theorem cell20_301773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_301773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301773 prefixEnd_301773 := by exact prefixLift 301773
  have htrace : WordTrace (prefixWord ++ tailWord_301773) baseStart_301773 baseEnd_301773 := by
    simpa [prefixWord, tailWord_301773, baseEnd_301773] using wordTrace_append hprefix tailTrace_301773
  have hstable : (prefixWord ++ tailWord_301773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301773).length < 2 ^ (prefixWord ++ tailWord_301773).sum := by decide
  have hdescent : baseEnd_301773 < baseStart_301773 := by decide
  rcases family_descends (prefixWord ++ tailWord_301773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301795 : List Nat := [1, 1, 1, 7, 1, 1, 2, 6]
def baseStart_301795 : Nat := 118140960795 + 301795 * 2 ^ 59
def prefixEnd_301795 : Nat := 4983230072969 + 3 ^ 40 * 301795 * 2
def baseEnd_301795 : Nat := 45915820481111691666541

theorem tailTrace_301795 : CollatzResearch.WordTrace tailWord_301795 prefixEnd_301795 45915820481111691666541 := by
  unfold tailWord_301795
  simp only [CollatzResearch.WordTrace]
  refine ⟨11007367941655732327602839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7338245294437154885068559 11007367941655732327602839)
  ·
    refine ⟨16511051912483598491404259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11007367941655732327602839 16511051912483598491404259)
    ·
      refine ⟨24766577868725397737106389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16511051912483598491404259 24766577868725397737106389)
      ·
        refine ⟨580466668798251509463431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 24766577868725397737106389 580466668798251509463431)
        ·
          refine ⟨870700003197377264195147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580466668798251509463431 870700003197377264195147)
          ·
            refine ⟨1306050004796065896292721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 870700003197377264195147 1306050004796065896292721)
            ·
              refine ⟨979537503597049422219541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1306050004796065896292721 979537503597049422219541)
              ·
                refine ⟨45915820481111691666541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 979537503597049422219541 45915820481111691666541)
                ·
                  rfl

theorem cell20_301795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 6].length) (baseStart_301795 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301795 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301795 prefixEnd_301795 := by exact prefixLift 301795
  have htrace : WordTrace (prefixWord ++ tailWord_301795) baseStart_301795 baseEnd_301795 := by
    simpa [prefixWord, tailWord_301795, baseEnd_301795] using wordTrace_append hprefix tailTrace_301795
  have hstable : (prefixWord ++ tailWord_301795).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301795).length < 2 ^ (prefixWord ++ tailWord_301795).sum := by decide
  have hdescent : baseEnd_301795 < baseStart_301795 := by decide
  rcases family_descends (prefixWord ++ tailWord_301795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301805 : List Nat := [1, 5, 1, 2, 1, 1, 2, 5, 2]
def baseStart_301805 : Nat := 118140960795 + 301805 * 2 ^ 59
def prefixEnd_301805 : Nat := 4983230072969 + 3 ^ 40 * 301805 * 2
def baseEnd_301805 : Nat := 137752025715819484666249

theorem tailTrace_301805 : CollatzResearch.WordTrace tailWord_301805 prefixEnd_301805 137752025715819484666249 := by
  unfold tailWord_301805
  simp only [CollatzResearch.WordTrace]
  refine ⟨11007732671619504035466869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7338488447746336023644579 11007732671619504035466869)
  ·
    refine ⟨1031974937964328503325019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11007732671619504035466869 1031974937964328503325019)
    ·
      refine ⟨1547962406946492754987529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1031974937964328503325019 1547962406946492754987529)
      ·
        refine ⟨1160971805209869566240647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1547962406946492754987529 1160971805209869566240647)
        ·
          refine ⟨1741457707814804349360971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1160971805209869566240647 1741457707814804349360971)
          ·
            refine ⟨2612186561722206524041457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1741457707814804349360971 2612186561722206524041457)
            ·
              refine ⟨1959139921291654893031093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2612186561722206524041457 1959139921291654893031093)
              ·
                refine ⟨183669367621092646221665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1959139921291654893031093 183669367621092646221665)
                ·
                  refine ⟨137752025715819484666249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183669367621092646221665 137752025715819484666249)
                  ·
                    rfl

theorem cell20_301805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_301805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301805 prefixEnd_301805 := by exact prefixLift 301805
  have htrace : WordTrace (prefixWord ++ tailWord_301805) baseStart_301805 baseEnd_301805 := by
    simpa [prefixWord, tailWord_301805, baseEnd_301805] using wordTrace_append hprefix tailTrace_301805
  have hstable : (prefixWord ++ tailWord_301805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301805).length < 2 ^ (prefixWord ++ tailWord_301805).sum := by decide
  have hdescent : baseEnd_301805 < baseStart_301805 := by decide
  rcases family_descends (prefixWord ++ tailWord_301805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301812 : List Nat := [2, 6, 1, 1, 10]
def baseStart_301812 : Nat := 118140960795 + 301812 * 2 ^ 59
def prefixEnd_301812 : Nat := 4983230072969 + 3 ^ 40 * 301812 * 2
def baseEnd_301812 : Nat := 1700681737118007054727

theorem tailTrace_301812 : CollatzResearch.WordTrace tailWord_301812 prefixEnd_301812 1700681737118007054727 := by
  unfold tailWord_301812
  simp only [CollatzResearch.WordTrace]
  refine ⟨5503993991297072115485845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7338658655062762820647793 5503993991297072115485845)
  ·
    refine ⟨257999718342050255413399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5503993991297072115485845 257999718342050255413399)
    ·
      refine ⟨386999577513075383120099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257999718342050255413399 386999577513075383120099)
      ·
        refine ⟨580499366269613074680149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386999577513075383120099 580499366269613074680149)
        ·
          refine ⟨1700681737118007054727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 580499366269613074680149 1700681737118007054727)
          ·
            rfl

theorem cell20_301812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 10].length) (baseStart_301812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301812 prefixEnd_301812 := by exact prefixLift 301812
  have htrace : WordTrace (prefixWord ++ tailWord_301812) baseStart_301812 baseEnd_301812 := by
    simpa [prefixWord, tailWord_301812, baseEnd_301812] using wordTrace_append hprefix tailTrace_301812
  have hstable : (prefixWord ++ tailWord_301812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301812).length < 2 ^ (prefixWord ++ tailWord_301812).sum := by decide
  have hdescent : baseEnd_301812 < baseStart_301812 := by decide
  rcases family_descends (prefixWord ++ tailWord_301812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301822 : List Nat := [4, 2, 2, 1, 2, 2, 1, 4, 2]
def baseStart_301822 : Nat := 118140960795 + 301822 * 2 ^ 59
def prefixEnd_301822 : Nat := 4983230072969 + 3 ^ 40 * 301822 * 2
def baseEnd_301822 : Nat := 137759784979042981099513

theorem tailTrace_301822 : CollatzResearch.WordTrace tailWord_301822 prefixEnd_301822 137759784979042981099513 := by
  unfold tailWord_301822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1376044089069739492354465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7338901808371943959223813 1376044089069739492354465)
  ·
    refine ⟨1032033066802304619265849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1376044089069739492354465 1032033066802304619265849)
    ·
      refine ⟨774024800101728464449387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1032033066802304619265849 774024800101728464449387)
      ·
        refine ⟨1161037200152592696674081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 774024800101728464449387 1161037200152592696674081)
        ·
          refine ⟨870777900114444522505561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1161037200152592696674081 870777900114444522505561)
          ·
            refine ⟨653083425085833391879171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 870777900114444522505561 653083425085833391879171)
            ·
              refine ⟨979625137628750087818757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 653083425085833391879171 979625137628750087818757)
              ·
                refine ⟨183679713305390641466017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 979625137628750087818757 183679713305390641466017)
                ·
                  refine ⟨137759784979042981099513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183679713305390641466017 137759784979042981099513)
                  ·
                    rfl

theorem cell20_301822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_301822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301822 prefixEnd_301822 := by exact prefixLift 301822
  have htrace : WordTrace (prefixWord ++ tailWord_301822) baseStart_301822 baseEnd_301822 := by
    simpa [prefixWord, tailWord_301822, baseEnd_301822] using wordTrace_append hprefix tailTrace_301822
  have hstable : (prefixWord ++ tailWord_301822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301822).length < 2 ^ (prefixWord ++ tailWord_301822).sum := by decide
  have hdescent : baseEnd_301822 < baseStart_301822 := by decide
  rcases family_descends (prefixWord ++ tailWord_301822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301860 : List Nat := [2, 3, 1, 3, 3, 1, 2, 3, 2]
def baseStart_301860 : Nat := 118140960795 + 301860 * 2 ^ 59
def prefixEnd_301860 : Nat := 4983230072969 + 3 ^ 40 * 301860 * 2
def baseEnd_301860 : Nat := 137777129214483737832691

theorem tailTrace_301860 : CollatzResearch.WordTrace tailWord_301860 prefixEnd_301860 137777129214483737832691 := by
  unfold tailWord_301860
  simp only [CollatzResearch.WordTrace]
  refine ⟨5504869343210124214359517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7339825790946832285812689 5504869343210124214359517)
  ·
    refine ⟨2064326003703796580384819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5504869343210124214359517 2064326003703796580384819)
    ·
      refine ⟨3096489005555694870577229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2064326003703796580384819 3096489005555694870577229)
      ·
        refine ⟨1161183377083385576466461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3096489005555694870577229 1161183377083385576466461)
        ·
          refine ⟨435443766406269591174923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1161183377083385576466461 435443766406269591174923)
          ·
            refine ⟨653165649609404386762385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435443766406269591174923 653165649609404386762385)
            ·
              refine ⟨489874237207053290071789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 653165649609404386762385 489874237207053290071789)
              ·
                refine ⟨183702838952644983776921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 489874237207053290071789 183702838952644983776921)
                ·
                  refine ⟨137777129214483737832691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183702838952644983776921 137777129214483737832691)
                  ·
                    rfl

theorem cell20_301860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_301860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301860 prefixEnd_301860 := by exact prefixLift 301860
  have htrace : WordTrace (prefixWord ++ tailWord_301860) baseStart_301860 baseEnd_301860 := by
    simpa [prefixWord, tailWord_301860, baseEnd_301860] using wordTrace_append hprefix tailTrace_301860
  have hstable : (prefixWord ++ tailWord_301860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301860).length < 2 ^ (prefixWord ++ tailWord_301860).sum := by decide
  have hdescent : baseEnd_301860 < baseStart_301860 := by decide
  rcases family_descends (prefixWord ++ tailWord_301860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301905 : List Nat := [1, 2, 2, 1, 7, 1, 2, 4]
def baseStart_301905 : Nat := 118140960795 + 301905 * 2 ^ 59
def prefixEnd_301905 : Nat := 4983230072969 + 3 ^ 40 * 301905 * 2
def baseEnd_301905 : Nat := 45932556146887860444169

theorem tailTrace_301905 : CollatzResearch.WordTrace tailWord_301905 prefixEnd_301905 45932556146887860444169 := by
  unfold tailWord_301905
  simp only [CollatzResearch.WordTrace]
  refine ⟨11011379971257221114107169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7340919980838147409404779 11011379971257221114107169)
  ·
    refine ⟨8258534978442915835580377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11011379971257221114107169 8258534978442915835580377)
    ·
      refine ⟨6193901233832186876685283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8258534978442915835580377 6193901233832186876685283)
      ·
        refine ⟨9290851850748280315027925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6193901233832186876685283 9290851850748280315027925)
        ·
          refine ⟨217754340251912819883467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 9290851850748280315027925 217754340251912819883467)
          ·
            refine ⟨326631510377869229825201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217754340251912819883467 326631510377869229825201)
            ·
              refine ⟨244973632783401922368901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326631510377869229825201 244973632783401922368901)
              ·
                refine ⟨45932556146887860444169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 244973632783401922368901 45932556146887860444169)
                ·
                  rfl

theorem cell20_301905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 4].length) (baseStart_301905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301905 prefixEnd_301905 := by exact prefixLift 301905
  have htrace : WordTrace (prefixWord ++ tailWord_301905) baseStart_301905 baseEnd_301905 := by
    simpa [prefixWord, tailWord_301905, baseEnd_301905] using wordTrace_append hprefix tailTrace_301905
  have hstable : (prefixWord ++ tailWord_301905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301905).length < 2 ^ (prefixWord ++ tailWord_301905).sum := by decide
  have hdescent : baseEnd_301905 < baseStart_301905 := by decide
  rcases family_descends (prefixWord ++ tailWord_301905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301991 : List Nat := [1, 1, 6, 1, 3, 2, 2, 2, 2]
def baseStart_301991 : Nat := 118140960795 + 301991 * 2 ^ 59
def prefixEnd_301991 : Nat := 4983230072969 + 3 ^ 40 * 301991 * 2
def baseEnd_301991 : Nat := 137836921184029504465489

theorem tailTrace_301991 : CollatzResearch.WordTrace tailWord_301991 prefixEnd_301991 137836921184029504465489 := by
  unfold tailWord_301991
  simp only [CollatzResearch.WordTrace]
  refine ⟨11014516648945657801737827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7343011099297105201158551 11014516648945657801737827)
  ·
    refine ⟨16521774973418486702606741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11014516648945657801737827 16521774973418486702606741)
    ·
      refine ⟨774458201878991564184691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16521774973418486702606741 774458201878991564184691)
      ·
        refine ⟨1161687302818487346277037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 774458201878991564184691 1161687302818487346277037)
        ·
          refine ⟨435632738556932754853889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1161687302818487346277037 435632738556932754853889)
          ·
            refine ⟨326724553917699566140417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 435632738556932754853889 326724553917699566140417)
            ·
              refine ⟨245043415438274674605313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326724553917699566140417 245043415438274674605313)
              ·
                refine ⟨183782561578706005953985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 245043415438274674605313 183782561578706005953985)
                ·
                  refine ⟨137836921184029504465489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183782561578706005953985 137836921184029504465489)
                  ·
                    rfl

theorem cell20_301991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 2, 2].length) (baseStart_301991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_301991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_301991 prefixEnd_301991 := by exact prefixLift 301991
  have htrace : WordTrace (prefixWord ++ tailWord_301991) baseStart_301991 baseEnd_301991 := by
    simpa [prefixWord, tailWord_301991, baseEnd_301991] using wordTrace_append hprefix tailTrace_301991
  have hstable : (prefixWord ++ tailWord_301991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301991).length < 2 ^ (prefixWord ++ tailWord_301991).sum := by decide
  have hdescent : baseEnd_301991 < baseStart_301991 := by decide
  rcases family_descends (prefixWord ++ tailWord_301991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302050 : List Nat := [3, 3, 3, 1, 1, 1, 2, 4, 2]
def baseStart_302050 : Nat := 118140960795 + 302050 * 2 ^ 59
def prefixEnd_302050 : Nat := 4983230072969 + 3 ^ 40 * 302050 * 2
def baseEnd_302050 : Nat := 137863850391687521498581

theorem tailTrace_302050 : CollatzResearch.WordTrace tailWord_302050 prefixEnd_302050 137863850391687521498581 := by
  unfold tailWord_302050
  simp only [CollatzResearch.WordTrace]
  refine ⟨2754167138932977719533901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7344445703821273918757069 2754167138932977719533901)
  ·
    refine ⟨1032812677099866644825213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2754167138932977719533901 1032812677099866644825213)
    ·
      refine ⟨387304753912449991809455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1032812677099866644825213 387304753912449991809455)
      ·
        refine ⟨580957130868674987714183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387304753912449991809455 580957130868674987714183)
        ·
          refine ⟨871435696303012481571275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580957130868674987714183 871435696303012481571275)
          ·
            refine ⟨1307153544454518722356913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 871435696303012481571275 1307153544454518722356913)
            ·
              refine ⟨980365158340889041767685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1307153544454518722356913 980365158340889041767685)
              ·
                refine ⟨183818467188916695331441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 980365158340889041767685 183818467188916695331441)
                ·
                  refine ⟨137863850391687521498581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183818467188916695331441 137863850391687521498581)
                  ·
                    rfl

theorem cell20_302050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_302050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302050 prefixEnd_302050 := by exact prefixLift 302050
  have htrace : WordTrace (prefixWord ++ tailWord_302050) baseStart_302050 baseEnd_302050 := by
    simpa [prefixWord, tailWord_302050, baseEnd_302050] using wordTrace_append hprefix tailTrace_302050
  have hstable : (prefixWord ++ tailWord_302050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302050).length < 2 ^ (prefixWord ++ tailWord_302050).sum := by decide
  have hdescent : baseEnd_302050 < baseStart_302050 := by decide
  rcases family_descends (prefixWord ++ tailWord_302050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302078 : List Nat := [4, 2, 2, 2, 2, 1, 1, 6]
def baseStart_302078 : Nat := 118140960795 + 302078 * 2 ^ 59
def prefixEnd_302078 : Nat := 4983230072969 + 3 ^ 40 * 302078 * 2
def baseEnd_302078 : Nat := 45958876784881289521711

theorem tailTrace_302078 : CollatzResearch.WordTrace tailWord_302078 prefixEnd_302078 45958876784881289521711 := by
  unfold tailWord_302078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1377211224953808957519361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7345126533086981106769925 1377211224953808957519361)
  ·
    refine ⟨1032908418715356718139521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1377211224953808957519361 1032908418715356718139521)
    ·
      refine ⟨774681314036517538604641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1032908418715356718139521 774681314036517538604641)
      ·
        refine ⟨581010985527388153953481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 774681314036517538604641 581010985527388153953481)
        ·
          refine ⟨435758239145541115465111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 581010985527388153953481 435758239145541115465111)
          ·
            refine ⟨653637358718311673197667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435758239145541115465111 653637358718311673197667)
            ·
              refine ⟨980456038077467509796501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 653637358718311673197667 980456038077467509796501)
              ·
                refine ⟨45958876784881289521711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 980456038077467509796501 45958876784881289521711)
                ·
                  rfl

theorem cell20_302078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_302078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302078 prefixEnd_302078 := by exact prefixLift 302078
  have htrace : WordTrace (prefixWord ++ tailWord_302078) baseStart_302078 baseEnd_302078 := by
    simpa [prefixWord, tailWord_302078, baseEnd_302078] using wordTrace_append hprefix tailTrace_302078
  have hstable : (prefixWord ++ tailWord_302078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302078).length < 2 ^ (prefixWord ++ tailWord_302078).sum := by decide
  have hdescent : baseEnd_302078 < baseStart_302078 := by decide
  rcases family_descends (prefixWord ++ tailWord_302078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302106 : List Nat := [3, 1, 1, 3, 1, 2, 2, 4, 3]
def baseStart_302106 : Nat := 118140960795 + 302106 * 2 ^ 59
def prefixEnd_302106 : Nat := 4983230072969 + 3 ^ 40 * 302106 * 2
def baseEnd_302106 : Nat := 137889410317600215631685

theorem tailTrace_302106 : CollatzResearch.WordTrace tailWord_302106 prefixEnd_302106 137889410317600215631685 := by
  unfold tailWord_302106
  simp only [CollatzResearch.WordTrace]
  refine ⟨2754677760882258110543543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7345807362352688294782781 2754677760882258110543543)
  ·
    refine ⟨4132016641323387165815315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2754677760882258110543543 4132016641323387165815315)
    ·
      refine ⟨6198024961985080748722973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4132016641323387165815315 6198024961985080748722973)
      ·
        refine ⟨2324259360744405280771115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6198024961985080748722973 2324259360744405280771115)
        ·
          refine ⟨3486389041116607921156673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2324259360744405280771115 3486389041116607921156673)
          ·
            refine ⟨2614791780837455940867505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3486389041116607921156673 2614791780837455940867505)
            ·
              refine ⟨1961093835628091955650629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2614791780837455940867505 1961093835628091955650629)
              ·
                refine ⟨367705094180267241684493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1961093835628091955650629 367705094180267241684493)
                ·
                  refine ⟨137889410317600215631685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 367705094180267241684493 137889410317600215631685)
                  ·
                    rfl

theorem cell20_302106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_302106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302106 prefixEnd_302106 := by exact prefixLift 302106
  have htrace : WordTrace (prefixWord ++ tailWord_302106) baseStart_302106 baseEnd_302106 := by
    simpa [prefixWord, tailWord_302106, baseEnd_302106] using wordTrace_append hprefix tailTrace_302106
  have hstable : (prefixWord ++ tailWord_302106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302106).length < 2 ^ (prefixWord ++ tailWord_302106).sum := by decide
  have hdescent : baseEnd_302106 < baseStart_302106 := by decide
  rcases family_descends (prefixWord ++ tailWord_302106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302109 : List Nat := [1, 4, 2, 2, 3, 2, 1, 1, 4]
def baseStart_302109 : Nat := 118140960795 + 302109 * 2 ^ 59
def prefixEnd_302109 : Nat := 4983230072969 + 3 ^ 40 * 302109 * 2
def baseEnd_302109 : Nat := 137890779599345538531673

theorem tailTrace_302109 : CollatzResearch.WordTrace tailWord_302109 prefixEnd_302109 137890779599345538531673 := by
  unfold tailWord_302109
  simp only [CollatzResearch.WordTrace]
  refine ⟨11018820462518163954533381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7345880308345442636355587 11018820462518163954533381)
  ·
    refine ⟨2066028836722155741475009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11018820462518163954533381 2066028836722155741475009)
    ·
      refine ⟨1549521627541616806106257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2066028836722155741475009 1549521627541616806106257)
      ·
        refine ⟨1162141220656212604579693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1549521627541616806106257 1162141220656212604579693)
        ·
          refine ⟨435802957746079726717385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1162141220656212604579693 435802957746079726717385)
          ·
            refine ⟨326852218309559795038039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 435802957746079726717385 326852218309559795038039)
            ·
              refine ⟨490278327464339692557059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326852218309559795038039 490278327464339692557059)
              ·
                refine ⟨735417491196509538835589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 490278327464339692557059 735417491196509538835589)
                ·
                  refine ⟨137890779599345538531673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 735417491196509538835589 137890779599345538531673)
                  ·
                    rfl

theorem cell20_302109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_302109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302109 prefixEnd_302109 := by exact prefixLift 302109
  have htrace : WordTrace (prefixWord ++ tailWord_302109) baseStart_302109 baseEnd_302109 := by
    simpa [prefixWord, tailWord_302109, baseEnd_302109] using wordTrace_append hprefix tailTrace_302109
  have hstable : (prefixWord ++ tailWord_302109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302109).length < 2 ^ (prefixWord ++ tailWord_302109).sum := by decide
  have hdescent : baseEnd_302109 < baseStart_302109 := by decide
  rcases family_descends (prefixWord ++ tailWord_302109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302119 : List Nat := [1, 1, 7, 1, 1, 3, 2, 1, 3]
def baseStart_302119 : Nat := 118140960795 + 302119 * 2 ^ 59
def prefixEnd_302119 : Nat := 4983230072969 + 3 ^ 40 * 302119 * 2
def baseEnd_302119 : Nat := 137895343871829948198299

theorem tailTrace_302119 : CollatzResearch.WordTrace tailWord_302119 prefixEnd_302119 137895343871829948198299 := by
  unfold tailWord_302119
  simp only [CollatzResearch.WordTrace]
  refine ⟨11019185192481935662397411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7346123461654623774931607 11019185192481935662397411)
  ·
    refine ⟨16528777788722903493596117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11019185192481935662397411 16528777788722903493596117)
    ·
      refine ⟨387393229423193050631159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 16528777788722903493596117 387393229423193050631159)
      ·
        refine ⟨581089844134789575946739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387393229423193050631159 581089844134789575946739)
        ·
          refine ⟨871634766202184363920109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 581089844134789575946739 871634766202184363920109)
          ·
            refine ⟨326863037325819136470041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 871634766202184363920109 326863037325819136470041)
            ·
              refine ⟨245147277994364352352531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326863037325819136470041 245147277994364352352531)
              ·
                refine ⟨367720916991546528528797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245147277994364352352531 367720916991546528528797)
                ·
                  refine ⟨137895343871829948198299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 367720916991546528528797 137895343871829948198299)
                  ·
                    rfl

theorem cell20_302119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 3].length) (baseStart_302119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302119 prefixEnd_302119 := by exact prefixLift 302119
  have htrace : WordTrace (prefixWord ++ tailWord_302119) baseStart_302119 baseEnd_302119 := by
    simpa [prefixWord, tailWord_302119, baseEnd_302119] using wordTrace_append hprefix tailTrace_302119
  have hstable : (prefixWord ++ tailWord_302119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302119).length < 2 ^ (prefixWord ++ tailWord_302119).sum := by decide
  have hdescent : baseEnd_302119 < baseStart_302119 := by decide
  rcases family_descends (prefixWord ++ tailWord_302119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302168 : List Nat := [2, 1, 2, 2, 1, 3, 3, 4, 2]
def baseStart_302168 : Nat := 118140960795 + 302168 * 2 ^ 59
def prefixEnd_302168 : Nat := 4983230072969 + 3 ^ 40 * 302168 * 2
def baseEnd_302168 : Nat := 137917708807003555564765

theorem tailTrace_302168 : CollatzResearch.WordTrace tailWord_302168 prefixEnd_302168 137917708807003555564765 := by
  unfold tailWord_302168
  simp only [CollatzResearch.WordTrace]
  refine ⟨5510486184652208515465579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7347314912869611353954105 5510486184652208515465579)
  ·
    refine ⟨8265729276978312773198369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5510486184652208515465579 8265729276978312773198369)
    ·
      refine ⟨6199296957733734579898777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8265729276978312773198369 6199296957733734579898777)
      ·
        refine ⟨4649472718300300934924083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6199296957733734579898777 4649472718300300934924083)
        ·
          refine ⟨6974209077450451402386125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4649472718300300934924083 6974209077450451402386125)
          ·
            refine ⟨2615328404043919275894797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6974209077450451402386125 2615328404043919275894797)
            ·
              refine ⟨980748151516469728460549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2615328404043919275894797 980748151516469728460549)
              ·
                refine ⟨183890278409338074086353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 980748151516469728460549 183890278409338074086353)
                ·
                  refine ⟨137917708807003555564765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183890278409338074086353 137917708807003555564765)
                  ·
                    rfl

theorem cell20_302168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 4, 2].length) (baseStart_302168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302168 prefixEnd_302168 := by exact prefixLift 302168
  have htrace : WordTrace (prefixWord ++ tailWord_302168) baseStart_302168 baseEnd_302168 := by
    simpa [prefixWord, tailWord_302168, baseEnd_302168] using wordTrace_append hprefix tailTrace_302168
  have hstable : (prefixWord ++ tailWord_302168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302168).length < 2 ^ (prefixWord ++ tailWord_302168).sum := by decide
  have hdescent : baseEnd_302168 < baseStart_302168 := by decide
  rcases family_descends (prefixWord ++ tailWord_302168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302189 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 6]
def baseStart_302189 : Nat := 118140960795 + 302189 * 2 ^ 59
def prefixEnd_302189 : Nat := 4983230072969 + 3 ^ 40 * 302189 * 2
def baseEnd_302189 : Nat := 137927293779220815864679

theorem tailTrace_302189 : CollatzResearch.WordTrace tailWord_302189 prefixEnd_302189 137927293779220815864679 := by
  unfold tailWord_302189
  simp only [CollatzResearch.WordTrace]
  refine ⟨11021738302228337617445621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7347825534818891744963747 11021738302228337617445621)
  ·
    refine ⟨1033287965833906651635527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11021738302228337617445621 1033287965833906651635527)
    ·
      refine ⟨1549931948750859977453291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1033287965833906651635527 1549931948750859977453291)
      ·
        refine ⟨2324897923126289966179937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1549931948750859977453291 2324897923126289966179937)
        ·
          refine ⟨1743673442344717474634953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2324897923126289966179937 1743673442344717474634953)
          ·
            refine ⟨1307755081758538105976215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1743673442344717474634953 1307755081758538105976215)
            ·
              refine ⟨1961632622637807158964323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1307755081758538105976215 1961632622637807158964323)
              ·
                refine ⟨2942448933956710738446485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1961632622637807158964323 2942448933956710738446485)
                ·
                  refine ⟨137927293779220815864679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2942448933956710738446485 137927293779220815864679)
                  ·
                    rfl

theorem cell20_302189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_302189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302189 prefixEnd_302189 := by exact prefixLift 302189
  have htrace : WordTrace (prefixWord ++ tailWord_302189) baseStart_302189 baseEnd_302189 := by
    simpa [prefixWord, tailWord_302189, baseEnd_302189] using wordTrace_append hprefix tailTrace_302189
  have hstable : (prefixWord ++ tailWord_302189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302189).length < 2 ^ (prefixWord ++ tailWord_302189).sum := by decide
  have hdescent : baseEnd_302189 < baseStart_302189 := by decide
  rcases family_descends (prefixWord ++ tailWord_302189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302216 : List Nat := [2, 1, 3, 4, 2, 2, 1, 2, 3]
def baseStart_302216 : Nat := 118140960795 + 302216 * 2 ^ 59
def prefixEnd_302216 : Nat := 4983230072969 + 3 ^ 40 * 302216 * 2
def baseEnd_302216 : Nat := 137939617314928721964569

theorem tailTrace_302216 : CollatzResearch.WordTrace tailWord_302216 prefixEnd_302216 137939617314928721964569 := by
  unfold tailWord_302216
  simp only [CollatzResearch.WordTrace]
  refine ⟨5511361536565260614339251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7348482048753680819119001 5511361536565260614339251)
  ·
    refine ⟨8267042304847890921508877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5511361536565260614339251 8267042304847890921508877)
    ·
      refine ⟨3100140864317959095565829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8267042304847890921508877 3100140864317959095565829)
      ·
        refine ⟨581276412059617330418593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3100140864317959095565829 581276412059617330418593)
        ·
          refine ⟨435957309044712997813945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 581276412059617330418593 435957309044712997813945)
          ·
            refine ⟨326967981783534748360459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 435957309044712997813945 326967981783534748360459)
            ·
              refine ⟨490451972675302122540689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326967981783534748360459 490451972675302122540689)
              ·
                refine ⟨367838979506476591905517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 490451972675302122540689 367838979506476591905517)
                ·
                  refine ⟨137939617314928721964569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 367838979506476591905517 137939617314928721964569)
                  ·
                    rfl

theorem cell20_302216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 3].length) (baseStart_302216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302216 prefixEnd_302216 := by exact prefixLift 302216
  have htrace : WordTrace (prefixWord ++ tailWord_302216) baseStart_302216 baseEnd_302216 := by
    simpa [prefixWord, tailWord_302216, baseEnd_302216] using wordTrace_append hprefix tailTrace_302216
  have hstable : (prefixWord ++ tailWord_302216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302216).length < 2 ^ (prefixWord ++ tailWord_302216).sum := by decide
  have hdescent : baseEnd_302216 < baseStart_302216 := by decide
  rcases family_descends (prefixWord ++ tailWord_302216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302237 : List Nat := [1, 4, 2, 1, 1, 2, 5, 1, 3]
def baseStart_302237 : Nat := 118140960795 + 302237 * 2 ^ 59
def prefixEnd_302237 : Nat := 4983230072969 + 3 ^ 40 * 302237 * 2
def baseEnd_302237 : Nat := 137949202287145982264483

theorem tailTrace_302237 : CollatzResearch.WordTrace tailWord_302237 prefixEnd_302237 137949202287145982264483 := by
  unfold tailWord_302237
  simp only [CollatzResearch.WordTrace]
  refine ⟨11023489006054441815192965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7348992670702961210128643 11023489006054441815192965)
  ·
    refine ⟨2066904188635207840348681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11023489006054441815192965 2066904188635207840348681)
    ·
      refine ⟨1550178141476405880261511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2066904188635207840348681 1550178141476405880261511)
      ·
        refine ⟨2325267212214608820392267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1550178141476405880261511 2325267212214608820392267)
        ·
          refine ⟨3487900818321913230588401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2325267212214608820392267 3487900818321913230588401)
          ·
            refine ⟨2615925613741434922941301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3487900818321913230588401 2615925613741434922941301)
            ·
              refine ⟨245243026288259524025747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2615925613741434922941301 245243026288259524025747)
              ·
                refine ⟨367864539432389286038621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245243026288259524025747 367864539432389286038621)
                ·
                  refine ⟨137949202287145982264483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 367864539432389286038621 137949202287145982264483)
                  ·
                    rfl

theorem cell20_302237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_302237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302237 prefixEnd_302237 := by exact prefixLift 302237
  have htrace : WordTrace (prefixWord ++ tailWord_302237) baseStart_302237 baseEnd_302237 := by
    simpa [prefixWord, tailWord_302237, baseEnd_302237] using wordTrace_append hprefix tailTrace_302237
  have hstable : (prefixWord ++ tailWord_302237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302237).length < 2 ^ (prefixWord ++ tailWord_302237).sum := by decide
  have hdescent : baseEnd_302237 < baseStart_302237 := by decide
  rcases family_descends (prefixWord ++ tailWord_302237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302274 : List Nat := [3, 5, 1, 1, 2, 1, 3, 2, 2]
def baseStart_302274 : Nat := 118140960795 + 302274 * 2 ^ 59
def prefixEnd_302274 : Nat := 4983230072969 + 3 ^ 40 * 302274 * 2
def baseEnd_302274 : Nat := 137966090095338298030999

theorem tailTrace_302274 : CollatzResearch.WordTrace tailWord_302274 prefixEnd_302274 137966090095338298030999 := by
  unfold tailWord_302274
  simp only [CollatzResearch.WordTrace]
  refine ⟨2756209626730099283572469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7349892337946931422859917 2756209626730099283572469)
  ·
    refine ⟨258394652505946807834919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2756209626730099283572469 258394652505946807834919)
    ·
      refine ⟨387591978758920211752379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258394652505946807834919 387591978758920211752379)
      ·
        refine ⟨581387968138380317628569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387591978758920211752379 581387968138380317628569)
        ·
          refine ⟨436040976103785238221427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 581387968138380317628569 436040976103785238221427)
          ·
            refine ⟨654061464155677857332141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436040976103785238221427 654061464155677857332141)
            ·
              refine ⟨245273049058379196499553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 654061464155677857332141 245273049058379196499553)
              ·
                refine ⟨183954786793784397374665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 245273049058379196499553 183954786793784397374665)
                ·
                  refine ⟨137966090095338298030999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183954786793784397374665 137966090095338298030999)
                  ·
                    rfl

theorem cell20_302274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_302274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302274 prefixEnd_302274 := by exact prefixLift 302274
  have htrace : WordTrace (prefixWord ++ tailWord_302274) baseStart_302274 baseEnd_302274 := by
    simpa [prefixWord, tailWord_302274, baseEnd_302274] using wordTrace_append hprefix tailTrace_302274
  have hstable : (prefixWord ++ tailWord_302274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302274).length < 2 ^ (prefixWord ++ tailWord_302274).sum := by decide
  have hdescent : baseEnd_302274 < baseStart_302274 := by decide
  rcases family_descends (prefixWord ++ tailWord_302274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302282 : List Nat := [3, 1, 2, 1, 3, 4, 1, 1, 4]
def baseStart_302282 : Nat := 118140960795 + 302282 * 2 ^ 59
def prefixEnd_302282 : Nat := 4983230072969 + 3 ^ 40 * 302282 * 2
def baseEnd_302282 : Nat := 137969741513325825764299

theorem tailTrace_302282 : CollatzResearch.WordTrace tailWord_302282 prefixEnd_302282 137969741513325825764299 := by
  unfold tailWord_302282
  simp only [CollatzResearch.WordTrace]
  refine ⟨2756282572722853625145275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7350086860594276333720733 2756282572722853625145275)
  ·
    refine ⟨4134423859084280437717913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2756282572722853625145275 4134423859084280437717913)
    ·
      refine ⟨3100817894313210328288435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4134423859084280437717913 3100817894313210328288435)
      ·
        refine ⟨4651226841469815492432653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3100817894313210328288435 4651226841469815492432653)
        ·
          refine ⟨1744210065551180809662245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4651226841469815492432653 1744210065551180809662245)
          ·
            refine ⟨327039387290846401811671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1744210065551180809662245 327039387290846401811671)
            ·
              refine ⟨490559080936269602717507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327039387290846401811671 490559080936269602717507)
              ·
                refine ⟨735838621404404404076261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 490559080936269602717507 735838621404404404076261)
                ·
                  refine ⟨137969741513325825764299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 735838621404404404076261 137969741513325825764299)
                  ·
                    rfl

theorem cell20_302282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_302282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302282 prefixEnd_302282 := by exact prefixLift 302282
  have htrace : WordTrace (prefixWord ++ tailWord_302282) baseStart_302282 baseEnd_302282 := by
    simpa [prefixWord, tailWord_302282, baseEnd_302282] using wordTrace_append hprefix tailTrace_302282
  have hstable : (prefixWord ++ tailWord_302282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302282).length < 2 ^ (prefixWord ++ tailWord_302282).sum := by decide
  have hdescent : baseEnd_302282 < baseStart_302282 := by decide
  rcases family_descends (prefixWord ++ tailWord_302282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302285 : List Nat := [1, 6, 2, 2, 1, 1, 2, 5]
def baseStart_302285 : Nat := 118140960795 + 302285 * 2 ^ 59
def prefixEnd_302285 : Nat := 4983230072969 + 3 ^ 40 * 302285 * 2
def baseEnd_302285 : Nat := 45990370265023716221429

theorem tailTrace_302285 : CollatzResearch.WordTrace tailWord_302285 prefixEnd_302285 45990370265023716221429 := by
  unfold tailWord_302285
  simp only [CollatzResearch.WordTrace]
  refine ⟨11025239709880546012940309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7350159806587030675293539 11025239709880546012940309)
  ·
    refine ⟨516808111400650594356577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11025239709880546012940309 516808111400650594356577)
    ·
      refine ⟨387606083550487945767433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 516808111400650594356577 387606083550487945767433)
      ·
        refine ⟨290704562662865959325575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 387606083550487945767433 290704562662865959325575)
        ·
          refine ⟨436056843994298938988363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290704562662865959325575 436056843994298938988363)
          ·
            refine ⟨654085265991448408482545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436056843994298938988363 654085265991448408482545)
            ·
              refine ⟨490563949493586306361909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 654085265991448408482545 490563949493586306361909)
              ·
                refine ⟨45990370265023716221429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 490563949493586306361909 45990370265023716221429)
                ·
                  rfl

theorem cell20_302285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 5].length) (baseStart_302285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302285 prefixEnd_302285 := by exact prefixLift 302285
  have htrace : WordTrace (prefixWord ++ tailWord_302285) baseStart_302285 baseEnd_302285 := by
    simpa [prefixWord, tailWord_302285, baseEnd_302285] using wordTrace_append hprefix tailTrace_302285
  have hstable : (prefixWord ++ tailWord_302285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302285).length < 2 ^ (prefixWord ++ tailWord_302285).sum := by decide
  have hdescent : baseEnd_302285 < baseStart_302285 := by decide
  rcases family_descends (prefixWord ++ tailWord_302285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302292 : List Nat := [2, 4, 1, 4, 1, 1, 1, 3, 3]
def baseStart_302292 : Nat := 118140960795 + 302292 * 2 ^ 59
def prefixEnd_302292 : Nat := 4983230072969 + 3 ^ 40 * 302292 * 2
def baseEnd_302292 : Nat := 137974305785810235430925

theorem tailTrace_302292 : CollatzResearch.WordTrace tailWord_302292 prefixEnd_302292 137974305785810235430925 := by
  unfold tailWord_302292
  simp only [CollatzResearch.WordTrace]
  refine ⟨5512747510427593104222565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7350330013903457472296753 5512747510427593104222565)
  ·
    refine ⟨1033640158205173707041731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5512747510427593104222565 1033640158205173707041731)
    ·
      refine ⟨1550460237307760560562597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1033640158205173707041731 1550460237307760560562597)
      ·
        refine ⟨290711294495205105105487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1550460237307760560562597 290711294495205105105487)
        ·
          refine ⟨436066941742807657658231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290711294495205105105487 436066941742807657658231)
          ·
            refine ⟨654100412614211486487347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436066941742807657658231 654100412614211486487347)
            ·
              refine ⟨981150618921317229731021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 654100412614211486487347 981150618921317229731021)
              ·
                refine ⟨367931482095493961149133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 981150618921317229731021 367931482095493961149133)
                ·
                  refine ⟨137974305785810235430925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 367931482095493961149133 137974305785810235430925)
                  ·
                    rfl

theorem cell20_302292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_302292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302292 prefixEnd_302292 := by exact prefixLift 302292
  have htrace : WordTrace (prefixWord ++ tailWord_302292) baseStart_302292 baseEnd_302292 := by
    simpa [prefixWord, tailWord_302292, baseEnd_302292] using wordTrace_append hprefix tailTrace_302292
  have hstable : (prefixWord ++ tailWord_302292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302292).length < 2 ^ (prefixWord ++ tailWord_302292).sum := by decide
  have hdescent : baseEnd_302292 < baseStart_302292 := by decide
  rcases family_descends (prefixWord ++ tailWord_302292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302337 : List Nat := [1, 2, 4, 1, 1, 3, 4, 2, 2]
def baseStart_302337 : Nat := 118140960795 + 302337 * 2 ^ 59
def prefixEnd_302337 : Nat := 4983230072969 + 3 ^ 40 * 302337 * 2
def baseEnd_302337 : Nat := 137994845011990078930741

theorem tailTrace_302337 : CollatzResearch.WordTrace tailWord_302337 prefixEnd_302337 137994845011990078930741 := by
  unfold tailWord_302337
  simp only [CollatzResearch.WordTrace]
  refine ⟨11027136305692158893833265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7351424203794772595888843 11027136305692158893833265)
  ·
    refine ⟨8270352229269119170374949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11027136305692158893833265 8270352229269119170374949)
    ·
      refine ⟨1550691042987959844445303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8270352229269119170374949 1550691042987959844445303)
      ·
        refine ⟨2326036564481939766667955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1550691042987959844445303 2326036564481939766667955)
        ·
          refine ⟨3489054846722909650001933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2326036564481939766667955 3489054846722909650001933)
          ·
            refine ⟨1308395567521091118750725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3489054846722909650001933 1308395567521091118750725)
            ·
              refine ⟨245324168910204584765761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1308395567521091118750725 245324168910204584765761)
              ·
                refine ⟨183993126682653438574321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 245324168910204584765761 183993126682653438574321)
                ·
                  refine ⟨137994845011990078930741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183993126682653438574321 137994845011990078930741)
                  ·
                    rfl

theorem cell20_302337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 2, 2].length) (baseStart_302337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302337 prefixEnd_302337 := by exact prefixLift 302337
  have htrace : WordTrace (prefixWord ++ tailWord_302337) baseStart_302337 baseEnd_302337 := by
    simpa [prefixWord, tailWord_302337, baseEnd_302337] using wordTrace_append hprefix tailTrace_302337
  have hstable : (prefixWord ++ tailWord_302337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302337).length < 2 ^ (prefixWord ++ tailWord_302337).sum := by decide
  have hdescent : baseEnd_302337 < baseStart_302337 := by decide
  rcases family_descends (prefixWord ++ tailWord_302337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302344 : List Nat := [2, 1, 3, 2, 5, 1, 1, 5]
def baseStart_302344 : Nat := 118140960795 + 302344 * 2 ^ 59
def prefixEnd_302344 : Nat := 4983230072969 + 3 ^ 40 * 302344 * 2
def baseEnd_302344 : Nat := 45999346667576388565793

theorem tailTrace_302344 : CollatzResearch.WordTrace tailWord_302344 prefixEnd_302344 45999346667576388565793 := by
  unfold tailWord_302344
  simp only [CollatzResearch.WordTrace]
  refine ⟨5513695808333399544669043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7351594411111199392892057 5513695808333399544669043)
  ·
    refine ⟨8270543712500099317003565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5513695808333399544669043 8270543712500099317003565)
    ·
      refine ⟨3101453892187537243876337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8270543712500099317003565 3101453892187537243876337)
      ·
        refine ⟨2326090419140652932907253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3101453892187537243876337 2326090419140652932907253)
        ·
          refine ⟨218070976794436212460055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2326090419140652932907253 218070976794436212460055)
          ·
            refine ⟨327106465191654318690083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218070976794436212460055 327106465191654318690083)
            ·
              refine ⟨490659697787481478035125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327106465191654318690083 490659697787481478035125)
              ·
                refine ⟨45999346667576388565793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 490659697787481478035125 45999346667576388565793)
                ·
                  rfl

theorem cell20_302344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 5].length) (baseStart_302344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302344 prefixEnd_302344 := by exact prefixLift 302344
  have htrace : WordTrace (prefixWord ++ tailWord_302344) baseStart_302344 baseEnd_302344 := by
    simpa [prefixWord, tailWord_302344, baseEnd_302344] using wordTrace_append hprefix tailTrace_302344
  have hstable : (prefixWord ++ tailWord_302344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302344).length < 2 ^ (prefixWord ++ tailWord_302344).sum := by decide
  have hdescent : baseEnd_302344 < baseStart_302344 := by decide
  rcases family_descends (prefixWord ++ tailWord_302344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302348 : List Nat := [2, 2, 1, 2, 2, 3, 3, 5]
def baseStart_302348 : Nat := 118140960795 + 302348 * 2 ^ 59
def prefixEnd_302348 : Nat := 4983230072969 + 3 ^ 40 * 302348 * 2
def baseEnd_302348 : Nat := 45999955237240976521343

theorem tailTrace_302348 : CollatzResearch.WordTrace tailWord_302348 prefixEnd_302348 45999955237240976521343 := by
  unfold tailWord_302348
  simp only [CollatzResearch.WordTrace]
  refine ⟨5513768754326153886241849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7351691672434871848322465 5513768754326153886241849)
  ·
    refine ⟨4135326565744615414681387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5513768754326153886241849 4135326565744615414681387)
    ·
      refine ⟨6202989848616923122022081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4135326565744615414681387 6202989848616923122022081)
      ·
        refine ⟨4652242386462692341516561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6202989848616923122022081 4652242386462692341516561)
        ·
          refine ⟨3489181789847019256137421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4652242386462692341516561 3489181789847019256137421)
          ·
            refine ⟨1308443171192632221051533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3489181789847019256137421 1308443171192632221051533)
            ·
              refine ⟨490666189197237082894325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1308443171192632221051533 490666189197237082894325)
              ·
                refine ⟨45999955237240976521343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 490666189197237082894325 45999955237240976521343)
                ·
                  rfl

theorem cell20_302348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 5].length) (baseStart_302348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302348 prefixEnd_302348 := by exact prefixLift 302348
  have htrace : WordTrace (prefixWord ++ tailWord_302348) baseStart_302348 baseEnd_302348 := by
    simpa [prefixWord, tailWord_302348, baseEnd_302348] using wordTrace_append hprefix tailTrace_302348
  have hstable : (prefixWord ++ tailWord_302348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302348).length < 2 ^ (prefixWord ++ tailWord_302348).sum := by decide
  have hdescent : baseEnd_302348 < baseStart_302348 := by decide
  rcases family_descends (prefixWord ++ tailWord_302348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302386 : List Nat := [3, 2, 1, 1, 4, 2, 7]
def baseStart_302386 : Nat := 118140960795 + 302386 * 2 ^ 59
def prefixEnd_302386 : Nat := 4983230072969 + 3 ^ 40 * 302386 * 2
def baseEnd_302386 : Nat := 15335245549684854033023

theorem tailTrace_302386 : CollatzResearch.WordTrace tailWord_302386 prefixEnd_302386 15335245549684854033023 := by
  unfold tailWord_302386
  simp only [CollatzResearch.WordTrace]
  refine ⟨2757230870628660065591753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7352615655009760174911341 2757230870628660065591753)
  ·
    refine ⟨2067923152971495049193815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2757230870628660065591753 2067923152971495049193815)
    ·
      refine ⟨3101884729457242573790723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2067923152971495049193815 3101884729457242573790723)
      ·
        refine ⟨4652827094185863860686085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3101884729457242573790723 4652827094185863860686085)
        ·
          refine ⟨872405080159849473878641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4652827094185863860686085 872405080159849473878641)
          ·
            refine ⟨654303810119887105408981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 872405080159849473878641 654303810119887105408981)
            ·
              refine ⟨15335245549684854033023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 654303810119887105408981 15335245549684854033023)
              ·
                rfl

theorem cell20_302386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 7].length) (baseStart_302386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302386 prefixEnd_302386 := by exact prefixLift 302386
  have htrace : WordTrace (prefixWord ++ tailWord_302386) baseStart_302386 baseEnd_302386 := by
    simpa [prefixWord, tailWord_302386, baseEnd_302386] using wordTrace_append hprefix tailTrace_302386
  have hstable : (prefixWord ++ tailWord_302386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302386).length < 2 ^ (prefixWord ++ tailWord_302386).sum := by decide
  have hdescent : baseEnd_302386 < baseStart_302386 := by decide
  rcases family_descends (prefixWord ++ tailWord_302386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302389 : List Nat := [1, 3, 3, 1, 2, 4, 1, 2, 3]
def baseStart_302389 : Nat := 118140960795 + 302389 * 2 ^ 59
def prefixEnd_302389 : Nat := 4983230072969 + 3 ^ 40 * 302389 * 2
def baseEnd_302389 : Nat := 138018579228909009197195

theorem tailTrace_302389 : CollatzResearch.WordTrace tailWord_302389 prefixEnd_302389 138018579228909009197195 := by
  unfold tailWord_302389
  simp only [CollatzResearch.WordTrace]
  refine ⟨11029032901503771774726221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7352688601002514516484147 11029032901503771774726221)
  ·
    refine ⟨4135887338063914415522333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11029032901503771774726221 4135887338063914415522333)
    ·
      refine ⟨1550957751773967905820875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4135887338063914415522333 1550957751773967905820875)
      ·
        refine ⟨2326436627660951858731313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1550957751773967905820875 2326436627660951858731313)
        ·
          refine ⟨1744827470745713894048485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2326436627660951858731313 1744827470745713894048485)
          ·
            refine ⟨327155150764821355134091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1744827470745713894048485 327155150764821355134091)
            ·
              refine ⟨490732726147232032701137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327155150764821355134091 490732726147232032701137)
              ·
                refine ⟨368049544610424024525853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 490732726147232032701137 368049544610424024525853)
                ·
                  refine ⟨138018579228909009197195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 368049544610424024525853 138018579228909009197195)
                  ·
                    rfl

theorem cell20_302389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_302389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302389 prefixEnd_302389 := by exact prefixLift 302389
  have htrace : WordTrace (prefixWord ++ tailWord_302389) baseStart_302389 baseEnd_302389 := by
    simpa [prefixWord, tailWord_302389, baseEnd_302389] using wordTrace_append hprefix tailTrace_302389
  have hstable : (prefixWord ++ tailWord_302389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302389).length < 2 ^ (prefixWord ++ tailWord_302389).sum := by decide
  have hdescent : baseEnd_302389 < baseStart_302389 := by decide
  rcases family_descends (prefixWord ++ tailWord_302389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302396 : List Nat := [2, 2, 2, 2, 1, 3, 2, 4, 2]
def baseStart_302396 : Nat := 118140960795 + 302396 * 2 ^ 59
def prefixEnd_302396 : Nat := 4983230072969 + 3 ^ 40 * 302396 * 2
def baseEnd_302396 : Nat := 138021774219648095963833

theorem tailTrace_302396 : CollatzResearch.WordTrace tailWord_302396 prefixEnd_302396 138021774219648095963833 := by
  unfold tailWord_302396
  simp only [CollatzResearch.WordTrace]
  refine ⟨5514644106239205985115521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7352858808318941313487361 5514644106239205985115521)
  ·
    refine ⟨4135983079679404488836641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5514644106239205985115521 4135983079679404488836641)
    ·
      refine ⟨3101987309759553366627481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4135983079679404488836641 3101987309759553366627481)
      ·
        refine ⟨2326490482319665024970611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3101987309759553366627481 2326490482319665024970611)
        ·
          refine ⟨3489735723479497537455917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2326490482319665024970611 3489735723479497537455917)
          ·
            refine ⟨1308650896304811576545969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3489735723479497537455917 1308650896304811576545969)
            ·
              refine ⟨981488172228608682409477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1308650896304811576545969 981488172228608682409477)
              ·
                refine ⟨184029032292864127951777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 981488172228608682409477 184029032292864127951777)
                ·
                  refine ⟨138021774219648095963833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184029032292864127951777 138021774219648095963833)
                  ·
                    rfl

theorem cell20_302396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 4, 2].length) (baseStart_302396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302396 prefixEnd_302396 := by exact prefixLift 302396
  have htrace : WordTrace (prefixWord ++ tailWord_302396) baseStart_302396 baseEnd_302396 := by
    simpa [prefixWord, tailWord_302396, baseEnd_302396] using wordTrace_append hprefix tailTrace_302396
  have hstable : (prefixWord ++ tailWord_302396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302396).length < 2 ^ (prefixWord ++ tailWord_302396).sum := by decide
  have hdescent : baseEnd_302396 < baseStart_302396 := by decide
  rcases family_descends (prefixWord ++ tailWord_302396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302465 : List Nat := [1, 2, 4, 3, 2, 1, 1, 3, 3]
def baseStart_302465 : Nat := 118140960795 + 302465 * 2 ^ 59
def prefixEnd_302465 : Nat := 4983230072969 + 3 ^ 40 * 302465 * 2
def baseEnd_302465 : Nat := 138053267699790522663551

theorem tailTrace_302465 : CollatzResearch.WordTrace tailWord_302465 prefixEnd_302465 138053267699790522663551 := by
  unfold tailWord_302465
  simp only [CollatzResearch.WordTrace]
  refine ⟨11031804849228436754492849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7354536566152291169661899 11031804849228436754492849)
  ·
    refine ⟨8273853636921327565869637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11031804849228436754492849 8273853636921327565869637)
    ·
      refine ⟨1551347556922748918600557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8273853636921327565869637 1551347556922748918600557)
      ·
        refine ⟨581755333846030844475209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1551347556922748918600557 581755333846030844475209)
        ·
          refine ⟨436316500384523133356407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 581755333846030844475209 436316500384523133356407)
          ·
            refine ⟨654474750576784700034611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436316500384523133356407 654474750576784700034611)
            ·
              refine ⟨981712125865177050051917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 654474750576784700034611 981712125865177050051917)
              ·
                refine ⟨368142047199441393769469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 981712125865177050051917 368142047199441393769469)
                ·
                  refine ⟨138053267699790522663551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 368142047199441393769469 138053267699790522663551)
                  ·
                    rfl

theorem cell20_302465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 3].length) (baseStart_302465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302465 prefixEnd_302465 := by exact prefixLift 302465
  have htrace : WordTrace (prefixWord ++ tailWord_302465) baseStart_302465 baseEnd_302465 := by
    simpa [prefixWord, tailWord_302465, baseEnd_302465] using wordTrace_append hprefix tailTrace_302465
  have hstable : (prefixWord ++ tailWord_302465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302465).length < 2 ^ (prefixWord ++ tailWord_302465).sum := by decide
  have hdescent : baseEnd_302465 < baseStart_302465 := by decide
  rcases family_descends (prefixWord ++ tailWord_302465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302476 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 6]
def baseStart_302476 : Nat := 118140960795 + 302476 * 2 ^ 59
def prefixEnd_302476 : Nat := 4983230072969 + 3 ^ 40 * 302476 * 2
def baseEnd_302476 : Nat := 138058288399523373296839

theorem tailTrace_302476 : CollatzResearch.WordTrace tailWord_302476 prefixEnd_302476 138058288399523373296839 := by
  unfold tailWord_302476
  simp only [CollatzResearch.WordTrace]
  refine ⟨5516103026094292816571641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7354804034792390422095521 5516103026094292816571641)
  ·
    refine ⟨4137077269570719612428731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5516103026094292816571641 4137077269570719612428731)
    ·
      refine ⟨6205615904356079418643097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4137077269570719612428731 6205615904356079418643097)
      ·
        refine ⟨4654211928267059563982323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6205615904356079418643097 4654211928267059563982323)
        ·
          refine ⟨6981317892400589345973485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4654211928267059563982323 6981317892400589345973485)
          ·
            refine ⟨2617994209650221004740057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6981317892400589345973485 2617994209650221004740057)
            ·
              refine ⟨1963495657237665753555043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2617994209650221004740057 1963495657237665753555043)
              ·
                refine ⟨2945243485856498630332565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1963495657237665753555043 2945243485856498630332565)
                ·
                  refine ⟨138058288399523373296839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2945243485856498630332565 138058288399523373296839)
                  ·
                    rfl

theorem cell20_302476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_302476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302476 prefixEnd_302476 := by exact prefixLift 302476
  have htrace : WordTrace (prefixWord ++ tailWord_302476) baseStart_302476 baseEnd_302476 := by
    simpa [prefixWord, tailWord_302476, baseEnd_302476] using wordTrace_append hprefix tailTrace_302476
  have hstable : (prefixWord ++ tailWord_302476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302476).length < 2 ^ (prefixWord ++ tailWord_302476).sum := by decide
  have hdescent : baseEnd_302476 < baseStart_302476 := by decide
  rcases family_descends (prefixWord ++ tailWord_302476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302517 : List Nat := [1, 3, 3, 2, 2, 3, 1, 5]
def baseStart_302517 : Nat := 118140960795 + 302517 * 2 ^ 59
def prefixEnd_302517 : Nat := 4983230072969 + 3 ^ 40 * 302517 * 2
def baseEnd_302517 : Nat := 46025667305569817643335

theorem tailTrace_302517 : CollatzResearch.WordTrace tailWord_302517 prefixEnd_302517 46025667305569817643335 := by
  unfold tailWord_302517
  simp only [CollatzResearch.WordTrace]
  refine ⟨11033701445040049635385805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7355800963360033090257203 11033701445040049635385805)
  ·
    refine ⟨4137638041890018613269677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11033701445040049635385805 4137638041890018613269677)
    ·
      refine ⟨1551614265708756979976129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4137638041890018613269677 1551614265708756979976129)
      ·
        refine ⟨1163710699281567734982097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1551614265708756979976129 1163710699281567734982097)
        ·
          refine ⟨872783024461175801236573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1163710699281567734982097 872783024461175801236573)
          ·
            refine ⟨327293634172940925463715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 872783024461175801236573 327293634172940925463715)
            ·
              refine ⟨490940451259411388195573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327293634172940925463715 490940451259411388195573)
              ·
                refine ⟨46025667305569817643335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 490940451259411388195573 46025667305569817643335)
                ·
                  rfl

theorem cell20_302517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 5].length) (baseStart_302517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302517 prefixEnd_302517 := by exact prefixLift 302517
  have htrace : WordTrace (prefixWord ++ tailWord_302517) baseStart_302517 baseEnd_302517 := by
    simpa [prefixWord, tailWord_302517, baseEnd_302517] using wordTrace_append hprefix tailTrace_302517
  have hstable : (prefixWord ++ tailWord_302517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302517).length < 2 ^ (prefixWord ++ tailWord_302517).sum := by decide
  have hdescent : baseEnd_302517 < baseStart_302517 := by decide
  rcases family_descends (prefixWord ++ tailWord_302517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302559 : List Nat := [1, 1, 2, 3, 3, 1, 9]
def baseStart_302559 : Nat := 118140960795 + 302559 * 2 ^ 59
def prefixEnd_302559 : Nat := 4983230072969 + 3 ^ 40 * 302559 * 2
def baseEnd_302559 : Nat := 15344019095682663725537

theorem tailTrace_302559 : CollatzResearch.WordTrace tailWord_302559 prefixEnd_302559 15344019095682663725537 := by
  unfold tailWord_302559
  simp only [CollatzResearch.WordTrace]
  refine ⟨11035233310887890808414731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7356822207258593872276487 11035233310887890808414731)
  ·
    refine ⟨16552849966331836212622097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11035233310887890808414731 16552849966331836212622097)
    ·
      refine ⟨12414637474748877159466573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16552849966331836212622097 12414637474748877159466573)
      ·
        refine ⟨4655489053030828934799965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12414637474748877159466573 4655489053030828934799965)
        ·
          refine ⟨1745808394886560850549987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4655489053030828934799965 1745808394886560850549987)
          ·
            refine ⟨2618712592329841275824981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1745808394886560850549987 2618712592329841275824981)
            ·
              refine ⟨15344019095682663725537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2618712592329841275824981 15344019095682663725537)
              ·
                rfl

theorem cell20_302559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 9].length) (baseStart_302559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302559 prefixEnd_302559 := by exact prefixLift 302559
  have htrace : WordTrace (prefixWord ++ tailWord_302559) baseStart_302559 baseEnd_302559 := by
    simpa [prefixWord, tailWord_302559, baseEnd_302559] using wordTrace_append hprefix tailTrace_302559
  have hstable : (prefixWord ++ tailWord_302559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302559).length < 2 ^ (prefixWord ++ tailWord_302559).sum := by decide
  have hdescent : baseEnd_302559 < baseStart_302559 := by decide
  rcases family_descends (prefixWord ++ tailWord_302559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302603 : List Nat := [1, 1, 1, 1, 8, 2, 1, 3, 2]
def baseStart_302603 : Nat := 118140960795 + 302603 * 2 ^ 59
def prefixEnd_302603 : Nat := 4983230072969 + 3 ^ 40 * 302603 * 2
def baseEnd_302603 : Nat := 138116254660075376062987

theorem tailTrace_302603 : CollatzResearch.WordTrace tailWord_302603 prefixEnd_302603 138116254660075376062987 := by
  unfold tailWord_302603
  simp only [CollatzResearch.WordTrace]
  refine ⟨11036838122728486323016463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7357892081818990882010975 11036838122728486323016463)
  ·
    refine ⟨16555257184092729484524695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11036838122728486323016463 16555257184092729484524695)
    ·
      refine ⟨24832885776139094226787043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16555257184092729484524695 24832885776139094226787043)
      ·
        refine ⟨37249328664208641340180565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24832885776139094226787043 37249328664208641340180565)
        ·
          refine ⟨436515570283695015705241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 37249328664208641340180565 436515570283695015705241)
          ·
            refine ⟨327386677712771261778931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 436515570283695015705241 327386677712771261778931)
            ·
              refine ⟨491080016569156892668397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327386677712771261778931 491080016569156892668397)
              ·
                refine ⟨184155006213433834750649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 491080016569156892668397 184155006213433834750649)
                ·
                  refine ⟨138116254660075376062987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184155006213433834750649 138116254660075376062987)
                  ·
                    rfl

theorem cell20_302603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 3, 2].length) (baseStart_302603 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302603 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302603 prefixEnd_302603 := by exact prefixLift 302603
  have htrace : WordTrace (prefixWord ++ tailWord_302603) baseStart_302603 baseEnd_302603 := by
    simpa [prefixWord, tailWord_302603, baseEnd_302603] using wordTrace_append hprefix tailTrace_302603
  have hstable : (prefixWord ++ tailWord_302603).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302603).length < 2 ^ (prefixWord ++ tailWord_302603).sum := by decide
  have hdescent : baseEnd_302603 < baseStart_302603 := by decide
  rcases family_descends (prefixWord ++ tailWord_302603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302621 : List Nat := [1, 4, 2, 2, 1, 1, 1, 3, 5]
def baseStart_302621 : Nat := 118140960795 + 302621 * 2 ^ 59
def prefixEnd_302621 : Nat := 4983230072969 + 3 ^ 40 * 302621 * 2
def baseEnd_302621 : Nat := 138124470350547313462913

theorem tailTrace_302621 : CollatzResearch.WordTrace tailWord_302621 prefixEnd_302621 138124470350547313462913 := by
  unfold tailWord_302621
  simp only [CollatzResearch.WordTrace]
  refine ⟨11037494636663275397171717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7358329757775516931447811 11037494636663275397171717)
  ·
    refine ⟨2069530244374364136969697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11037494636663275397171717 2069530244374364136969697)
    ·
      refine ⟨1552147683280773102727273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2069530244374364136969697 1552147683280773102727273)
      ·
        refine ⟨1164110762460579827045455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1552147683280773102727273 1164110762460579827045455)
        ·
          refine ⟨1746166143690869740568183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1164110762460579827045455 1746166143690869740568183)
          ·
            refine ⟨2619249215536304610852275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1746166143690869740568183 2619249215536304610852275)
            ·
              refine ⟨3928873823304456916278413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2619249215536304610852275 3928873823304456916278413)
              ·
                refine ⟨1473327683739171343604405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3928873823304456916278413 1473327683739171343604405)
                ·
                  refine ⟨138124470350547313462913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1473327683739171343604405 138124470350547313462913)
                  ·
                    rfl

theorem cell20_302621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_302621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302621 prefixEnd_302621 := by exact prefixLift 302621
  have htrace : WordTrace (prefixWord ++ tailWord_302621) baseStart_302621 baseEnd_302621 := by
    simpa [prefixWord, tailWord_302621, baseEnd_302621] using wordTrace_append hprefix tailTrace_302621
  have hstable : (prefixWord ++ tailWord_302621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302621).length < 2 ^ (prefixWord ++ tailWord_302621).sum := by decide
  have hdescent : baseEnd_302621 < baseStart_302621 := by decide
  rcases family_descends (prefixWord ++ tailWord_302621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302624 : List Nat := [2, 1, 1, 6, 1, 3, 1, 1, 4]
def baseStart_302624 : Nat := 118140960795 + 302624 * 2 ^ 59
def prefixEnd_302624 : Nat := 4983230072969 + 3 ^ 40 * 302624 * 2
def baseEnd_302624 : Nat := 138125839632292636362901

theorem tailTrace_302624 : CollatzResearch.WordTrace tailWord_302624 prefixEnd_302624 138125839632292636362901 := by
  unfold tailWord_302624
  simp only [CollatzResearch.WordTrace]
  refine ⟨5518802027826203454765463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7358402703768271273020617 5518802027826203454765463)
  ·
    refine ⟨8278203041739305182148195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5518802027826203454765463 8278203041739305182148195)
    ·
      refine ⟨12417304562608957773222293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8278203041739305182148195 12417304562608957773222293)
      ·
        refine ⟨582061151372294895619795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12417304562608957773222293 582061151372294895619795)
        ·
          refine ⟨873091727058442343429693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582061151372294895619795 873091727058442343429693)
          ·
            refine ⟨327409397646915878786135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 873091727058442343429693 327409397646915878786135)
            ·
              refine ⟨491114096470373818179203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327409397646915878786135 491114096470373818179203)
              ·
                refine ⟨736671144705560727268805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 491114096470373818179203 736671144705560727268805)
                ·
                  refine ⟨138125839632292636362901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 736671144705560727268805 138125839632292636362901)
                  ·
                    rfl

theorem cell20_302624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 4].length) (baseStart_302624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302624 prefixEnd_302624 := by exact prefixLift 302624
  have htrace : WordTrace (prefixWord ++ tailWord_302624) baseStart_302624 baseEnd_302624 := by
    simpa [prefixWord, tailWord_302624, baseEnd_302624] using wordTrace_append hprefix tailTrace_302624
  have hstable : (prefixWord ++ tailWord_302624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302624).length < 2 ^ (prefixWord ++ tailWord_302624).sum := by decide
  have hdescent : baseEnd_302624 < baseStart_302624 := by decide
  rcases family_descends (prefixWord ++ tailWord_302624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302669 : List Nat := [1, 6, 1, 1, 4, 7]
def baseStart_302669 : Nat := 118140960795 + 302669 * 2 ^ 59
def prefixEnd_302669 : Nat := 4983230072969 + 3 ^ 40 * 302669 * 2
def baseEnd_302669 : Nat := 5116532550313795550471

theorem tailTrace_302669 : CollatzResearch.WordTrace tailWord_302669 prefixEnd_302669 5116532550313795550471 := by
  unfold tailWord_302669
  simp only [CollatzResearch.WordTrace]
  refine ⟨11039245340489379594919061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7359496893659586396612707 11039245340489379594919061)
  ·
    refine ⟨517464625335439668511831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11039245340489379594919061 517464625335439668511831)
    ·
      refine ⟨776196938003159502767747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 517464625335439668511831 776196938003159502767747)
      ·
        refine ⟨1164295407004739254151621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 776196938003159502767747 1164295407004739254151621)
        ·
          refine ⟨218305388813388610153429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1164295407004739254151621 218305388813388610153429)
          ·
            refine ⟨5116532550313795550471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 218305388813388610153429 5116532550313795550471)
            ·
              rfl

theorem cell20_302669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 7].length) (baseStart_302669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302669 prefixEnd_302669 := by exact prefixLift 302669
  have htrace : WordTrace (prefixWord ++ tailWord_302669) baseStart_302669 baseEnd_302669 := by
    simpa [prefixWord, tailWord_302669, baseEnd_302669] using wordTrace_append hprefix tailTrace_302669
  have hstable : (prefixWord ++ tailWord_302669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302669).length < 2 ^ (prefixWord ++ tailWord_302669).sum := by decide
  have hdescent : baseEnd_302669 < baseStart_302669 := by decide
  rcases family_descends (prefixWord ++ tailWord_302669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302676 : List Nat := [2, 4, 1, 1, 1, 2, 4, 2, 3]
def baseStart_302676 : Nat := 118140960795 + 302676 * 2 ^ 59
def prefixEnd_302676 : Nat := 4983230072969 + 3 ^ 40 * 302676 * 2
def baseEnd_302676 : Nat := 138149573849211566629355

theorem tailTrace_302676 : CollatzResearch.WordTrace tailWord_302676 prefixEnd_302676 138149573849211566629355 := by
  unfold tailWord_302676
  simp only [CollatzResearch.WordTrace]
  refine ⟨5519750325732009895211941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7359667100976013193615921 5519750325732009895211941)
  ·
    refine ⟨1034953186074751855352239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5519750325732009895211941 1034953186074751855352239)
    ·
      refine ⟨1552429779112127783028359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1034953186074751855352239 1552429779112127783028359)
      ·
        refine ⟨2328644668668191674542539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1552429779112127783028359 2328644668668191674542539)
        ·
          refine ⟨3492967003002287511813809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2328644668668191674542539 3492967003002287511813809)
          ·
            refine ⟨2619725252251715633860357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3492967003002287511813809 2619725252251715633860357)
            ·
              refine ⟨491198484797196681348817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2619725252251715633860357 491198484797196681348817)
              ·
                refine ⟨368398863597897511011613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 491198484797196681348817 368398863597897511011613)
                ·
                  refine ⟨138149573849211566629355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 368398863597897511011613 138149573849211566629355)
                  ·
                    rfl

theorem cell20_302676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_302676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302676 prefixEnd_302676 := by exact prefixLift 302676
  have htrace : WordTrace (prefixWord ++ tailWord_302676) baseStart_302676 baseEnd_302676 := by
    simpa [prefixWord, tailWord_302676, baseEnd_302676] using wordTrace_append hprefix tailTrace_302676
  have hstable : (prefixWord ++ tailWord_302676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302676).length < 2 ^ (prefixWord ++ tailWord_302676).sum := by decide
  have hdescent : baseEnd_302676 < baseStart_302676 := by decide
  rcases family_descends (prefixWord ++ tailWord_302676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302679 : List Nat := [1, 1, 3, 2, 2, 5, 2, 2, 2]
def baseStart_302679 : Nat := 118140960795 + 302679 * 2 ^ 59
def prefixEnd_302679 : Nat := 4983230072969 + 3 ^ 40 * 302679 * 2
def baseEnd_302679 : Nat := 138150943130956889529343

theorem tailTrace_302679 : CollatzResearch.WordTrace tailWord_302679 prefixEnd_302679 138150943130956889529343 := by
  unfold tailWord_302679
  simp only [CollatzResearch.WordTrace]
  refine ⟨11039610070453151302783091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7359740046968767535188727 11039610070453151302783091)
  ·
    refine ⟨16559415105679726954174637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11039610070453151302783091 16559415105679726954174637)
    ·
      refine ⟨6209780664629897607815489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16559415105679726954174637 6209780664629897607815489)
      ·
        refine ⟨4657335498472423205861617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6209780664629897607815489 4657335498472423205861617)
        ·
          refine ⟨3493001623854317404396213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4657335498472423205861617 3493001623854317404396213)
          ·
            refine ⟨327468902236342256662145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3493001623854317404396213 327468902236342256662145)
            ·
              refine ⟨245601676677256692496609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 327468902236342256662145 245601676677256692496609)
              ·
                refine ⟨184201257507942519372457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 245601676677256692496609 184201257507942519372457)
                ·
                  refine ⟨138150943130956889529343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184201257507942519372457 138150943130956889529343)
                  ·
                    rfl

theorem cell20_302679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 2, 2].length) (baseStart_302679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302679 prefixEnd_302679 := by exact prefixLift 302679
  have htrace : WordTrace (prefixWord ++ tailWord_302679) baseStart_302679 baseEnd_302679 := by
    simpa [prefixWord, tailWord_302679, baseEnd_302679] using wordTrace_append hprefix tailTrace_302679
  have hstable : (prefixWord ++ tailWord_302679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302679).length < 2 ^ (prefixWord ++ tailWord_302679).sum := by decide
  have hdescent : baseEnd_302679 < baseStart_302679 := by decide
  rcases family_descends (prefixWord ++ tailWord_302679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302697 : List Nat := [1, 2, 1, 1, 1, 4, 4, 3, 3]
def baseStart_302697 : Nat := 118140960795 + 302697 * 2 ^ 59
def prefixEnd_302697 : Nat := 4983230072969 + 3 ^ 40 * 302697 * 2
def baseEnd_302697 : Nat := 138159158821428826929269

theorem tailTrace_302697 : CollatzResearch.WordTrace tailWord_302697 prefixEnd_302697 138159158821428826929269 := by
  unfold tailWord_302697
  simp only [CollatzResearch.WordTrace]
  refine ⟨11040266584387940376938345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7360177722925293584625563 11040266584387940376938345)
  ·
    refine ⟨8280199938290955282703759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11040266584387940376938345 8280199938290955282703759)
    ·
      refine ⟨12420299907436432924055639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8280199938290955282703759 12420299907436432924055639)
      ·
        refine ⟨18630449861154649386083459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12420299907436432924055639 18630449861154649386083459)
        ·
          refine ⟨27945674791731974079125189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18630449861154649386083459 27945674791731974079125189)
          ·
            refine ⟨5239814023449745139835973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27945674791731974079125189 5239814023449745139835973)
            ·
              refine ⟨982465129396827213719245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5239814023449745139835973 982465129396827213719245)
              ·
                refine ⟨368424423523810205144717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 982465129396827213719245 368424423523810205144717)
                ·
                  refine ⟨138159158821428826929269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 368424423523810205144717 138159158821428826929269)
                  ·
                    rfl

theorem cell20_302697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 3].length) (baseStart_302697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302697 prefixEnd_302697 := by exact prefixLift 302697
  have htrace : WordTrace (prefixWord ++ tailWord_302697) baseStart_302697 baseEnd_302697 := by
    simpa [prefixWord, tailWord_302697, baseEnd_302697] using wordTrace_append hprefix tailTrace_302697
  have hstable : (prefixWord ++ tailWord_302697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302697).length < 2 ^ (prefixWord ++ tailWord_302697).sum := by decide
  have hdescent : baseEnd_302697 < baseStart_302697 := by decide
  rcases family_descends (prefixWord ++ tailWord_302697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302704 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 6]
def baseStart_302704 : Nat := 118140960795 + 302704 * 2 ^ 59
def prefixEnd_302704 : Nat := 4983230072969 + 3 ^ 40 * 302704 * 2
def baseEnd_302704 : Nat := 138162353812167913695907

theorem tailTrace_302704 : CollatzResearch.WordTrace tailWord_302704 prefixEnd_302704 138162353812167913695907 := by
  unfold tailWord_302704
  simp only [CollatzResearch.WordTrace]
  refine ⟨5520260947681290286221583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7360347930241720381628777 5520260947681290286221583)
  ·
    refine ⟨8280391421521935429332375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5520260947681290286221583 8280391421521935429332375)
    ·
      refine ⟨12420587132282903143998563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8280391421521935429332375 12420587132282903143998563)
      ·
        refine ⟨18630880698424354715997845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12420587132282903143998563 18630880698424354715997845)
        ·
          refine ⟨873322532738641627312399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18630880698424354715997845 873322532738641627312399)
          ·
            refine ⟨1309983799107962440968599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 873322532738641627312399 1309983799107962440968599)
            ·
              refine ⟨1964975698661943661452899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1309983799107962440968599 1964975698661943661452899)
              ·
                refine ⟨2947463547992915492179349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1964975698661943661452899 2947463547992915492179349)
                ·
                  refine ⟨138162353812167913695907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2947463547992915492179349 138162353812167913695907)
                  ·
                    rfl

theorem cell20_302704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_302704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302704 prefixEnd_302704 := by exact prefixLift 302704
  have htrace : WordTrace (prefixWord ++ tailWord_302704) baseStart_302704 baseEnd_302704 := by
    simpa [prefixWord, tailWord_302704, baseEnd_302704] using wordTrace_append hprefix tailTrace_302704
  have hstable : (prefixWord ++ tailWord_302704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302704).length < 2 ^ (prefixWord ++ tailWord_302704).sum := by decide
  have hdescent : baseEnd_302704 < baseStart_302704 := by decide
  rcases family_descends (prefixWord ++ tailWord_302704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302738 : List Nat := [3, 2, 3, 1, 3, 1, 2, 1, 4]
def baseStart_302738 : Nat := 118140960795 + 302738 * 2 ^ 59
def prefixEnd_302738 : Nat := 4983230072969 + 3 ^ 40 * 302738 * 2
def baseEnd_302738 : Nat := 138177872338614906562435

theorem tailTrace_302738 : CollatzResearch.WordTrace tailWord_302738 prefixEnd_302738 138177872338614906562435 := by
  unfold tailWord_302738
  simp only [CollatzResearch.WordTrace]
  refine ⟨2760440494309851094795217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7361174651492936252787245 2760440494309851094795217)
  ·
    refine ⟨2070330370732388321096413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2760440494309851094795217 2070330370732388321096413)
    ·
      refine ⟨776373889024645620411155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2070330370732388321096413 776373889024645620411155)
      ·
        refine ⟨1164560833536968430616733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 776373889024645620411155 1164560833536968430616733)
        ·
          refine ⟨436710312576363161481275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1164560833536968430616733 436710312576363161481275)
          ·
            refine ⟨655065468864544742221913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436710312576363161481275 655065468864544742221913)
            ·
              refine ⟨491299101648408556666435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 655065468864544742221913 491299101648408556666435)
              ·
                refine ⟨736948652472612834999653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 491299101648408556666435 736948652472612834999653)
                ·
                  refine ⟨138177872338614906562435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 736948652472612834999653 138177872338614906562435)
                  ·
                    rfl

theorem cell20_302738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_302738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302738 prefixEnd_302738 := by exact prefixLift 302738
  have htrace : WordTrace (prefixWord ++ tailWord_302738) baseStart_302738 baseEnd_302738 := by
    simpa [prefixWord, tailWord_302738, baseEnd_302738] using wordTrace_append hprefix tailTrace_302738
  have hstable : (prefixWord ++ tailWord_302738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302738).length < 2 ^ (prefixWord ++ tailWord_302738).sum := by decide
  have hdescent : baseEnd_302738 < baseStart_302738 := by decide
  rcases family_descends (prefixWord ++ tailWord_302738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302749 : List Nat := [1, 4, 2, 1, 1, 1, 1, 9]
def baseStart_302749 : Nat := 118140960795 + 302749 * 2 ^ 59
def prefixEnd_302749 : Nat := 4983230072969 + 3 ^ 40 * 302749 * 2
def baseEnd_302749 : Nat := 46060964346115919065241

theorem tailTrace_302749 : CollatzResearch.WordTrace tailWord_302749 prefixEnd_302749 46060964346115919065241 := by
  unfold tailWord_302749
  simp only [CollatzResearch.WordTrace]
  refine ⟨11042163180199553257831301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7361442120133035505220867 11042163180199553257831301)
  ·
    refine ⟨2070405596287416235843369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11042163180199553257831301 2070405596287416235843369)
    ·
      refine ⟨1552804197215562176882527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2070405596287416235843369 1552804197215562176882527)
      ·
        refine ⟨2329206295823343265323791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1552804197215562176882527 2329206295823343265323791)
        ·
          refine ⟨3493809443735014897985687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2329206295823343265323791 3493809443735014897985687)
          ·
            refine ⟨5240714165602522346978531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3493809443735014897985687 5240714165602522346978531)
            ·
              refine ⟨7861071248403783520467797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5240714165602522346978531 7861071248403783520467797)
              ·
                refine ⟨46060964346115919065241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7861071248403783520467797 46060964346115919065241)
                ·
                  rfl

theorem cell20_302749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 9].length) (baseStart_302749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302749 prefixEnd_302749 := by exact prefixLift 302749
  have htrace : WordTrace (prefixWord ++ tailWord_302749) baseStart_302749 baseEnd_302749 := by
    simpa [prefixWord, tailWord_302749, baseEnd_302749] using wordTrace_append hprefix tailTrace_302749
  have hstable : (prefixWord ++ tailWord_302749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302749).length < 2 ^ (prefixWord ++ tailWord_302749).sum := by decide
  have hdescent : baseEnd_302749 < baseStart_302749 := by decide
  rcases family_descends (prefixWord ++ tailWord_302749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302804 : List Nat := [2, 4, 1, 3, 1, 1, 1, 7]
def baseStart_302804 : Nat := 118140960795 + 302804 * 2 ^ 59
def prefixEnd_302804 : Nat := 4983230072969 + 3 ^ 40 * 302804 * 2
def baseEnd_302804 : Nat := 46069332179004003454055

theorem tailTrace_302804 : CollatzResearch.WordTrace tailWord_302804 prefixEnd_302804 46069332179004003454055 := by
  unfold tailWord_302804
  simp only [CollatzResearch.WordTrace]
  refine ⟨5522084597500148825541733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7362779463333531767388977 5522084597500148825541733)
  ·
    refine ⟨1035390862031277904789075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5522084597500148825541733 1035390862031277904789075)
    ·
      refine ⟨1553086293046916857183613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1035390862031277904789075 1553086293046916857183613)
      ·
        refine ⟨582407359892593821443855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1553086293046916857183613 582407359892593821443855)
        ·
          refine ⟨873611039838890732165783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582407359892593821443855 873611039838890732165783)
          ·
            refine ⟨1310416559758336098248675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 873611039838890732165783 1310416559758336098248675)
            ·
              refine ⟨1965624839637504147373013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1310416559758336098248675 1965624839637504147373013)
              ·
                refine ⟨46069332179004003454055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1965624839637504147373013 46069332179004003454055)
                ·
                  rfl

theorem cell20_302804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 7].length) (baseStart_302804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302804 prefixEnd_302804 := by exact prefixLift 302804
  have htrace : WordTrace (prefixWord ++ tailWord_302804) baseStart_302804 baseEnd_302804 := by
    simpa [prefixWord, tailWord_302804, baseEnd_302804] using wordTrace_append hprefix tailTrace_302804
  have hstable : (prefixWord ++ tailWord_302804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302804).length < 2 ^ (prefixWord ++ tailWord_302804).sum := by decide
  have hdescent : baseEnd_302804 < baseStart_302804 := by decide
  rcases family_descends (prefixWord ++ tailWord_302804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302832 : List Nat := [2, 1, 1, 1, 3, 1, 2, 4, 5]
def baseStart_302832 : Nat := 118140960795 + 302832 * 2 ^ 59
def prefixEnd_302832 : Nat := 4983230072969 + 3 ^ 40 * 302832 * 2
def baseEnd_302832 : Nat := 138220776499968357428717

theorem tailTrace_302832 : CollatzResearch.WordTrace tailWord_302832 prefixEnd_302832 138220776499968357428717 := by
  unfold tailWord_302832
  simp only [CollatzResearch.WordTrace]
  refine ⟨5522595219449429216551375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7363460292599238955401833 5522595219449429216551375)
  ·
    refine ⟨8283892829174143824827063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5522595219449429216551375 8283892829174143824827063)
    ·
      refine ⟨12425839243761215737240595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8283892829174143824827063 12425839243761215737240595)
      ·
        refine ⟨18638758865641823605860893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12425839243761215737240595 18638758865641823605860893)
        ·
          refine ⟨6989534574615683852197835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18638758865641823605860893 6989534574615683852197835)
          ·
            refine ⟨10484301861923525778296753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6989534574615683852197835 10484301861923525778296753)
            ·
              refine ⟨7863226396442644333722565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10484301861923525778296753 7863226396442644333722565)
              ·
                refine ⟨1474354949332995812572981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7863226396442644333722565 1474354949332995812572981)
                ·
                  refine ⟨138220776499968357428717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1474354949332995812572981 138220776499968357428717)
                  ·
                    rfl

theorem cell20_302832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_302832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302832 prefixEnd_302832 := by exact prefixLift 302832
  have htrace : WordTrace (prefixWord ++ tailWord_302832) baseStart_302832 baseEnd_302832 := by
    simpa [prefixWord, tailWord_302832, baseEnd_302832] using wordTrace_append hprefix tailTrace_302832
  have hstable : (prefixWord ++ tailWord_302832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302832).length < 2 ^ (prefixWord ++ tailWord_302832).sum := by decide
  have hdescent : baseEnd_302832 < baseStart_302832 := by decide
  rcases family_descends (prefixWord ++ tailWord_302832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302849 : List Nat := [1, 2, 4, 1, 1, 1, 3, 4, 3]
def baseStart_302849 : Nat := 118140960795 + 302849 * 2 ^ 59
def prefixEnd_302849 : Nat := 4983230072969 + 3 ^ 40 * 302849 * 2
def baseEnd_302849 : Nat := 138228535763191853861981

theorem tailTrace_302849 : CollatzResearch.WordTrace tailWord_302849 prefixEnd_302849 138228535763191853861981 := by
  unfold tailWord_302849
  simp only [CollatzResearch.WordTrace]
  refine ⟨11045810479837270336471601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7363873653224846890981067 11045810479837270336471601)
  ·
    refine ⟨8284357859877952752353701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11045810479837270336471601 8284357859877952752353701)
    ·
      refine ⟨1553317098727116141066319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8284357859877952752353701 1553317098727116141066319)
      ·
        refine ⟨2329975648090674211599479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1553317098727116141066319 2329975648090674211599479)
        ·
          refine ⟨3494963472136011317399219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2329975648090674211599479 3494963472136011317399219)
          ·
            refine ⟨5242445208204016976098829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3494963472136011317399219 5242445208204016976098829)
            ·
              refine ⟨1965916953076506366037061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5242445208204016976098829 1965916953076506366037061)
              ·
                refine ⟨368609428701844943631949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1965916953076506366037061 368609428701844943631949)
                ·
                  refine ⟨138228535763191853861981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 368609428701844943631949 138228535763191853861981)
                  ·
                    rfl

theorem cell20_302849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 3].length) (baseStart_302849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302849 prefixEnd_302849 := by exact prefixLift 302849
  have htrace : WordTrace (prefixWord ++ tailWord_302849) baseStart_302849 baseEnd_302849 := by
    simpa [prefixWord, tailWord_302849, baseEnd_302849] using wordTrace_append hprefix tailTrace_302849
  have hstable : (prefixWord ++ tailWord_302849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302849).length < 2 ^ (prefixWord ++ tailWord_302849).sum := by decide
  have hdescent : baseEnd_302849 < baseStart_302849 := by decide
  rcases family_descends (prefixWord ++ tailWord_302849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302852 : List Nat := [2, 3, 2, 2, 1, 3, 1, 4, 2]
def baseStart_302852 : Nat := 118140960795 + 302852 * 2 ^ 59
def prefixEnd_302852 : Nat := 4983230072969 + 3 ^ 40 * 302852 * 2
def baseEnd_302852 : Nat := 138229905044937176761969

theorem tailTrace_302852 : CollatzResearch.WordTrace tailWord_302852 prefixEnd_302852 138229905044937176761969 := by
  unfold tailWord_302852
  simp only [CollatzResearch.WordTrace]
  refine ⟨5522959949413200924415405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7363946599217601232553873 5522959949413200924415405)
  ·
    refine ⟨2071109981029950346655777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5522959949413200924415405 2071109981029950346655777)
    ·
      refine ⟨1553332485772462759991833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2071109981029950346655777 1553332485772462759991833)
      ·
        refine ⟨1164999364329347069993875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1553332485772462759991833 1164999364329347069993875)
        ·
          refine ⟨1747499046494020604990813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1164999364329347069993875 1747499046494020604990813)
          ·
            refine ⟨655312142435257726871555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1747499046494020604990813 655312142435257726871555)
            ·
              refine ⟨982968213652886590307333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 655312142435257726871555 982968213652886590307333)
              ·
                refine ⟨184306540059916235682625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 982968213652886590307333 184306540059916235682625)
                ·
                  refine ⟨138229905044937176761969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184306540059916235682625 138229905044937176761969)
                  ·
                    rfl

theorem cell20_302852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_302852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302852 prefixEnd_302852 := by exact prefixLift 302852
  have htrace : WordTrace (prefixWord ++ tailWord_302852) baseStart_302852 baseEnd_302852 := by
    simpa [prefixWord, tailWord_302852, baseEnd_302852] using wordTrace_append hprefix tailTrace_302852
  have hstable : (prefixWord ++ tailWord_302852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302852).length < 2 ^ (prefixWord ++ tailWord_302852).sum := by decide
  have hdescent : baseEnd_302852 < baseStart_302852 := by decide
  rcases family_descends (prefixWord ++ tailWord_302852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302856 : List Nat := [2, 1, 3, 2, 2, 1, 2, 3, 4]
def baseStart_302856 : Nat := 118140960795 + 302856 * 2 ^ 59
def prefixEnd_302856 : Nat := 4983230072969 + 3 ^ 40 * 302856 * 2
def baseEnd_302856 : Nat := 138231730753930940628619

theorem tailTrace_302856 : CollatzResearch.WordTrace tailWord_302856 prefixEnd_302856 138231730753930940628619 := by
  unfold tailWord_302856
  simp only [CollatzResearch.WordTrace]
  refine ⟨5523032895405955265988211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7364043860541273687984281 5523032895405955265988211)
  ·
    refine ⟨8284549343108932898982317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5523032895405955265988211 8284549343108932898982317)
    ·
      refine ⟨3106706003665849837118369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8284549343108932898982317 3106706003665849837118369)
      ·
        refine ⟨2330029502749387377838777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3106706003665849837118369 2330029502749387377838777)
        ·
          refine ⟨1747522127062040533379083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2330029502749387377838777 1747522127062040533379083)
          ·
            refine ⟨2621283190593060800068625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1747522127062040533379083 2621283190593060800068625)
            ·
              refine ⟨1965962392944795600051469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2621283190593060800068625 1965962392944795600051469)
              ·
                refine ⟨737235897354298350019301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1965962392944795600051469 737235897354298350019301)
                ·
                  refine ⟨138231730753930940628619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 737235897354298350019301 138231730753930940628619)
                  ·
                    rfl

theorem cell20_302856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_302856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302856 prefixEnd_302856 := by exact prefixLift 302856
  have htrace : WordTrace (prefixWord ++ tailWord_302856) baseStart_302856 baseEnd_302856 := by
    simpa [prefixWord, tailWord_302856, baseEnd_302856] using wordTrace_append hprefix tailTrace_302856
  have hstable : (prefixWord ++ tailWord_302856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302856).length < 2 ^ (prefixWord ++ tailWord_302856).sum := by decide
  have hdescent : baseEnd_302856 < baseStart_302856 := by decide
  rcases family_descends (prefixWord ++ tailWord_302856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302880 : List Nat := [2, 1, 1, 5, 1, 1, 5, 4]
def baseStart_302880 : Nat := 118140960795 + 302880 * 2 ^ 59
def prefixEnd_302880 : Nat := 4983230072969 + 3 ^ 40 * 302880 * 2
def baseEnd_302880 : Nat := 46080895002631174609507

theorem tailTrace_302880 : CollatzResearch.WordTrace tailWord_302880 prefixEnd_302880 46080895002631174609507 := by
  unfold tailWord_302880
  simp only [CollatzResearch.WordTrace]
  refine ⟨5523470571362481315425047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7364627428483308420566729 5523470571362481315425047)
  ·
    refine ⟨8285205857043721973137571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5523470571362481315425047 8285205857043721973137571)
    ·
      refine ⟨12427808785565582959706357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8285205857043721973137571 12427808785565582959706357)
      ·
        refine ⟨1165107073646773402472471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12427808785565582959706357 1165107073646773402472471)
        ·
          refine ⟨1747660610470160103708707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1165107073646773402472471 1747660610470160103708707)
          ·
            refine ⟨2621490915705240155563061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1747660610470160103708707 2621490915705240155563061)
            ·
              refine ⟨245764773347366264584037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2621490915705240155563061 245764773347366264584037)
              ·
                refine ⟨46080895002631174609507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 245764773347366264584037 46080895002631174609507)
                ·
                  rfl

theorem cell20_302880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 4].length) (baseStart_302880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302880 prefixEnd_302880 := by exact prefixLift 302880
  have htrace : WordTrace (prefixWord ++ tailWord_302880) baseStart_302880 baseEnd_302880 := by
    simpa [prefixWord, tailWord_302880, baseEnd_302880] using wordTrace_append hprefix tailTrace_302880
  have hstable : (prefixWord ++ tailWord_302880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302880).length < 2 ^ (prefixWord ++ tailWord_302880).sum := by decide
  have hdescent : baseEnd_302880 < baseStart_302880 := by decide
  rcases family_descends (prefixWord ++ tailWord_302880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302904 : List Nat := [2, 1, 2, 1, 3, 5, 1, 2, 3]
def baseStart_302904 : Nat := 118140960795 + 302904 * 2 ^ 59
def prefixEnd_302904 : Nat := 4983230072969 + 3 ^ 40 * 302904 * 2
def baseEnd_302904 : Nat := 138253639261856107028423

theorem tailTrace_302904 : CollatzResearch.WordTrace tailWord_302904 prefixEnd_302904 138253639261856107028423 := by
  unfold tailWord_302904
  simp only [CollatzResearch.WordTrace]
  refine ⟨5523908247319007364861883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7365210996425343153149177 5523908247319007364861883)
  ·
    refine ⟨8285862370978511047292825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5523908247319007364861883 8285862370978511047292825)
    ·
      refine ⟨6214396778233883285469619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8285862370978511047292825 6214396778233883285469619)
      ·
        refine ⟨9321595167350824928204429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6214396778233883285469619 9321595167350824928204429)
        ·
          refine ⟨3495598187756559348076661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9321595167350824928204429 3495598187756559348076661)
          ·
            refine ⟨327712330102177438882187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3495598187756559348076661 327712330102177438882187)
            ·
              refine ⟨491568495153266158323281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327712330102177438882187 491568495153266158323281)
              ·
                refine ⟨368676371364949618742461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 491568495153266158323281 368676371364949618742461)
                ·
                  refine ⟨138253639261856107028423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 368676371364949618742461 138253639261856107028423)
                  ·
                    rfl

theorem cell20_302904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 3].length) (baseStart_302904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302904 prefixEnd_302904 := by exact prefixLift 302904
  have htrace : WordTrace (prefixWord ++ tailWord_302904) baseStart_302904 baseEnd_302904 := by
    simpa [prefixWord, tailWord_302904, baseEnd_302904] using wordTrace_append hprefix tailTrace_302904
  have hstable : (prefixWord ++ tailWord_302904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302904).length < 2 ^ (prefixWord ++ tailWord_302904).sum := by decide
  have hdescent : baseEnd_302904 < baseStart_302904 := by decide
  rcases family_descends (prefixWord ++ tailWord_302904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302911 : List Nat := [1, 1, 2, 2, 6, 1, 2, 1, 4]
def baseStart_302911 : Nat := 118140960795 + 302911 * 2 ^ 59
def prefixEnd_302911 : Nat := 4983230072969 + 3 ^ 40 * 302911 * 2
def baseEnd_302911 : Nat := 138256834252595193795061

theorem tailTrace_302911 : CollatzResearch.WordTrace tailWord_302911 prefixEnd_302911 138256834252595193795061 := by
  unfold tailWord_302911
  simp only [CollatzResearch.WordTrace]
  refine ⟨11048071805612654925228587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7365381203741769950152391 11048071805612654925228587)
  ·
    refine ⟨16572107708418982387842881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11048071805612654925228587 16572107708418982387842881)
    ·
      refine ⟨12429080781314236790882161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16572107708418982387842881 12429080781314236790882161)
      ·
        refine ⟨9321810585985677593161621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12429080781314236790882161 9321810585985677593161621)
        ·
          refine ⟨436959871218078637179451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9321810585985677593161621 436959871218078637179451)
          ·
            refine ⟨655439806827117955769177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436959871218078637179451 655439806827117955769177)
            ·
              refine ⟨491579855120338466826883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 655439806827117955769177 491579855120338466826883)
              ·
                refine ⟨737369782680507700240325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 491579855120338466826883 737369782680507700240325)
                ·
                  refine ⟨138256834252595193795061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 737369782680507700240325 138256834252595193795061)
                  ·
                    rfl

theorem cell20_302911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 4].length) (baseStart_302911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302911 prefixEnd_302911 := by exact prefixLift 302911
  have htrace : WordTrace (prefixWord ++ tailWord_302911) baseStart_302911 baseEnd_302911 := by
    simpa [prefixWord, tailWord_302911, baseEnd_302911] using wordTrace_append hprefix tailTrace_302911
  have hstable : (prefixWord ++ tailWord_302911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302911).length < 2 ^ (prefixWord ++ tailWord_302911).sum := by decide
  have hdescent : baseEnd_302911 < baseStart_302911 := by decide
  rcases family_descends (prefixWord ++ tailWord_302911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302935 : List Nat := [1, 1, 3, 2, 5, 2, 2, 4]
def baseStart_302935 : Nat := 118140960795 + 302935 * 2 ^ 59
def prefixEnd_302935 : Nat := 4983230072969 + 3 ^ 40 * 302935 * 2
def baseEnd_302935 : Nat := 46089262835519258998321

theorem tailTrace_302935 : CollatzResearch.WordTrace tailWord_302935 prefixEnd_302935 46089262835519258998321 := by
  unfold tailWord_302935
  simp only [CollatzResearch.WordTrace]
  refine ⟨11048947157525707024102259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7365964771683804682734839 11048947157525707024102259)
  ·
    refine ⟨16573420736288560536153389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11048947157525707024102259 16573420736288560536153389)
    ·
      refine ⟨6215032776108210201057521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16573420736288560536153389 6215032776108210201057521)
      ·
        refine ⟨4661274582081157650793141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6215032776108210201057521 4661274582081157650793141)
        ·
          refine ⟨436994492070108529761857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4661274582081157650793141 436994492070108529761857)
          ·
            refine ⟨327745869052581397321393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 436994492070108529761857 327745869052581397321393)
            ·
              refine ⟨245809401789436047991045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 327745869052581397321393 245809401789436047991045)
              ·
                refine ⟨46089262835519258998321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 245809401789436047991045 46089262835519258998321)
                ·
                  rfl

theorem cell20_302935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 4].length) (baseStart_302935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302935 prefixEnd_302935 := by exact prefixLift 302935
  have htrace : WordTrace (prefixWord ++ tailWord_302935) baseStart_302935 baseEnd_302935 := by
    simpa [prefixWord, tailWord_302935, baseEnd_302935] using wordTrace_append hprefix tailTrace_302935
  have hstable : (prefixWord ++ tailWord_302935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302935).length < 2 ^ (prefixWord ++ tailWord_302935).sum := by decide
  have hdescent : baseEnd_302935 < baseStart_302935 := by decide
  rcases family_descends (prefixWord ++ tailWord_302935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302953 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 6]
def baseStart_302953 : Nat := 118140960795 + 302953 * 2 ^ 59
def prefixEnd_302953 : Nat := 4983230072969 + 3 ^ 40 * 302953 * 2
def baseEnd_302953 : Nat := 138276004197029714394889

theorem tailTrace_302953 : CollatzResearch.WordTrace tailWord_302953 prefixEnd_302953 138276004197029714394889 := by
  unfold tailWord_302953
  simp only [CollatzResearch.WordTrace]
  refine ⟨11049603671460496098257513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7366402447640330732171675 11049603671460496098257513)
  ·
    refine ⟨8287202753595372073693135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11049603671460496098257513 8287202753595372073693135)
    ·
      refine ⟨12430804130393058110539703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8287202753595372073693135 12430804130393058110539703)
      ·
        refine ⟨18646206195589587165809555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12430804130393058110539703 18646206195589587165809555)
        ·
          refine ⟨27969309293384380748714333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18646206195589587165809555 27969309293384380748714333)
          ·
            refine ⟨10488490985019142780767875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27969309293384380748714333 10488490985019142780767875)
            ·
              refine ⟨15732736477528714171151813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10488490985019142780767875 15732736477528714171151813)
              ·
                refine ⟨2949888089536633907090965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15732736477528714171151813 2949888089536633907090965)
                ·
                  refine ⟨138276004197029714394889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2949888089536633907090965 138276004197029714394889)
                  ·
                    rfl

theorem cell20_302953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_302953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302953 prefixEnd_302953 := by exact prefixLift 302953
  have htrace : WordTrace (prefixWord ++ tailWord_302953) baseStart_302953 baseEnd_302953 := by
    simpa [prefixWord, tailWord_302953, baseEnd_302953] using wordTrace_append hprefix tailTrace_302953
  have hstable : (prefixWord ++ tailWord_302953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302953).length < 2 ^ (prefixWord ++ tailWord_302953).sum := by decide
  have hdescent : baseEnd_302953 < baseStart_302953 := by decide
  rcases family_descends (prefixWord ++ tailWord_302953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302970 : List Nat := [3, 1, 1, 1, 1, 1, 7, 1, 4]
def baseStart_302970 : Nat := 118140960795 + 302970 * 2 ^ 59
def prefixEnd_302970 : Nat := 4983230072969 + 3 ^ 40 * 302970 * 2
def baseEnd_302970 : Nat := 138283763460253210828153

theorem tailTrace_302970 : CollatzResearch.WordTrace tailWord_302970 prefixEnd_302970 138283763460253210828153 := by
  unfold tailWord_302970
  simp only [CollatzResearch.WordTrace]
  refine ⟨2762555928099727000406591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7366815808265938667750909 2762555928099727000406591)
  ·
    refine ⟨4143833892149590500609887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2762555928099727000406591 4143833892149590500609887)
    ·
      refine ⟨6215750838224385750914831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4143833892149590500609887 6215750838224385750914831)
      ·
        refine ⟨9323626257336578626372247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6215750838224385750914831 9323626257336578626372247)
        ·
          refine ⟨13985439386004867939558371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9323626257336578626372247 13985439386004867939558371)
          ·
            refine ⟨20978159079007301909337557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13985439386004867939558371 20978159079007301909337557)
            ·
              refine ⟨491675603414233638500099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 20978159079007301909337557 491675603414233638500099)
              ·
                refine ⟨737513405121350457750149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 491675603414233638500099 737513405121350457750149)
                ·
                  refine ⟨138283763460253210828153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 737513405121350457750149 138283763460253210828153)
                  ·
                    rfl

theorem cell20_302970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_302970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302970 prefixEnd_302970 := by exact prefixLift 302970
  have htrace : WordTrace (prefixWord ++ tailWord_302970) baseStart_302970 baseEnd_302970 := by
    simpa [prefixWord, tailWord_302970, baseEnd_302970] using wordTrace_append hprefix tailTrace_302970
  have hstable : (prefixWord ++ tailWord_302970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302970).length < 2 ^ (prefixWord ++ tailWord_302970).sum := by decide
  have hdescent : baseEnd_302970 < baseStart_302970 := by decide
  rcases family_descends (prefixWord ++ tailWord_302970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302980 : List Nat := [2, 3, 2, 1, 1, 1, 6, 1, 3]
def baseStart_302980 : Nat := 118140960795 + 302980 * 2 ^ 59
def prefixEnd_302980 : Nat := 4983230072969 + 3 ^ 40 * 302980 * 2
def baseEnd_302980 : Nat := 138288327732737620494779

theorem tailTrace_302980 : CollatzResearch.WordTrace tailWord_302980 prefixEnd_302980 138288327732737620494779 := by
  unfold tailWord_302980
  simp only [CollatzResearch.WordTrace]
  refine ⟨5525294221181339854745197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7367058961575119806326929 5525294221181339854745197)
  ·
    refine ⟨2071985332943002445529449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5525294221181339854745197 2071985332943002445529449)
    ·
      refine ⟨1553988999707251834147087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2071985332943002445529449 1553988999707251834147087)
      ·
        refine ⟨2330983499560877751220631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1553988999707251834147087 2330983499560877751220631)
        ·
          refine ⟨3496475249341316626830947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2330983499560877751220631 3496475249341316626830947)
          ·
            refine ⟨5244712874011974940246421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3496475249341316626830947 5244712874011974940246421)
            ·
              refine ⟨245845915969311325324051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5244712874011974940246421 245845915969311325324051)
              ·
                refine ⟨368768873953966987986077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245845915969311325324051 368768873953966987986077)
                ·
                  refine ⟨138288327732737620494779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 368768873953966987986077 138288327732737620494779)
                  ·
                    rfl

theorem cell20_302980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_302980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302980 prefixEnd_302980 := by exact prefixLift 302980
  have htrace : WordTrace (prefixWord ++ tailWord_302980) baseStart_302980 baseEnd_302980 := by
    simpa [prefixWord, tailWord_302980, baseEnd_302980] using wordTrace_append hprefix tailTrace_302980
  have hstable : (prefixWord ++ tailWord_302980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302980).length < 2 ^ (prefixWord ++ tailWord_302980).sum := by decide
  have hdescent : baseEnd_302980 < baseStart_302980 := by decide
  rcases family_descends (prefixWord ++ tailWord_302980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302994 : List Nat := [3, 2, 3, 2, 1, 1, 2, 6]
def baseStart_302994 : Nat := 118140960795 + 302994 * 2 ^ 59
def prefixEnd_302994 : Nat := 4983230072969 + 3 ^ 40 * 302994 * 2
def baseEnd_302994 : Nat := 46098239238071931342685

theorem tailTrace_302994 : CollatzResearch.WordTrace tailWord_302994 prefixEnd_302994 46098239238071931342685 := by
  unfold tailWord_302994
  simp only [CollatzResearch.WordTrace]
  refine ⟨2762774766077990025125009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7367399376207973400333357 2762774766077990025125009)
  ·
    refine ⟨2072081074558492518843757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2762774766077990025125009 2072081074558492518843757)
    ·
      refine ⟨777030402959434694566409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2072081074558492518843757 777030402959434694566409)
      ·
        refine ⟨582772802219576020924807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 777030402959434694566409 582772802219576020924807)
        ·
          refine ⟨874159203329364031387211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582772802219576020924807 874159203329364031387211)
          ·
            refine ⟨1311238804994046047080817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 874159203329364031387211 1311238804994046047080817)
            ·
              refine ⟨983429103745534535310613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1311238804994046047080817 983429103745534535310613)
              ·
                refine ⟨46098239238071931342685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 983429103745534535310613 46098239238071931342685)
                ·
                  rfl

theorem cell20_302994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_302994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_302994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_302994 prefixEnd_302994 := by exact prefixLift 302994
  have htrace : WordTrace (prefixWord ++ tailWord_302994) baseStart_302994 baseEnd_302994 := by
    simpa [prefixWord, tailWord_302994, baseEnd_302994] using wordTrace_append hprefix tailTrace_302994
  have hstable : (prefixWord ++ tailWord_302994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302994).length < 2 ^ (prefixWord ++ tailWord_302994).sum := by decide
  have hdescent : baseEnd_302994 < baseStart_302994 := by decide
  rcases family_descends (prefixWord ++ tailWord_302994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303015 : List Nat := [1, 1, 6, 1, 2, 9]
def baseStart_303015 : Nat := 118140960795 + 303015 * 2 ^ 59
def prefixEnd_303015 : Nat := 4983230072969 + 3 ^ 40 * 303015 * 2
def baseEnd_303015 : Nat := 5122381580979002012147

theorem tailTrace_303015 : CollatzResearch.WordTrace tailWord_303015 prefixEnd_303015 5122381580979002012147 := by
  unfold tailWord_303015
  simp only [CollatzResearch.WordTrace]
  refine ⟨11051864997235880687014499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7367909998157253791342999 11051864997235880687014499)
  ·
    refine ⟨16577797495853821030521749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11051864997235880687014499 16577797495853821030521749)
    ·
      refine ⟨777084257618147860805707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16577797495853821030521749 777084257618147860805707)
      ·
        refine ⟨1165626386427221791208561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 777084257618147860805707 1165626386427221791208561)
        ·
          refine ⟨874219789820416343406421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1165626386427221791208561 874219789820416343406421)
          ·
            refine ⟨5122381580979002012147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 874219789820416343406421 5122381580979002012147)
            ·
              rfl

theorem cell20_303015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 9].length) (baseStart_303015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303015 prefixEnd_303015 := by exact prefixLift 303015
  have htrace : WordTrace (prefixWord ++ tailWord_303015) baseStart_303015 baseEnd_303015 := by
    simpa [prefixWord, tailWord_303015, baseEnd_303015] using wordTrace_append hprefix tailTrace_303015
  have hstable : (prefixWord ++ tailWord_303015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303015).length < 2 ^ (prefixWord ++ tailWord_303015).sum := by decide
  have hdescent : baseEnd_303015 < baseStart_303015 := by decide
  rcases family_descends (prefixWord ++ tailWord_303015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303028 : List Nat := [2, 5, 2, 1, 2, 2, 1, 5]
def baseStart_303028 : Nat := 118140960795 + 303028 * 2 ^ 59
def prefixEnd_303028 : Nat := 4983230072969 + 3 ^ 40 * 303028 * 2
def baseEnd_303028 : Nat := 46103412080220928964861

theorem tailTrace_303028 : CollatzResearch.WordTrace tailWord_303028 prefixEnd_303028 46103412080220928964861 := by
  unfold tailWord_303028
  simp only [CollatzResearch.WordTrace]
  refine ⟨5526169573094391953618869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7368226097459189271491825 5526169573094391953618869)
  ·
    refine ⟨518078397477599245651769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5526169573094391953618869 518078397477599245651769)
    ·
      refine ⟨388558798108199434238827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 518078397477599245651769 388558798108199434238827)
      ·
        refine ⟨582838197162299151358241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388558798108199434238827 582838197162299151358241)
        ·
          refine ⟨437128647871724363518681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 582838197162299151358241 437128647871724363518681)
          ·
            refine ⟨327846485903793272639011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 437128647871724363518681 327846485903793272639011)
            ·
              refine ⟨491769728855689908958517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327846485903793272639011 491769728855689908958517)
              ·
                refine ⟨46103412080220928964861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 491769728855689908958517 46103412080220928964861)
                ·
                  rfl

theorem cell20_303028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 5].length) (baseStart_303028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303028 prefixEnd_303028 := by exact prefixLift 303028
  have htrace : WordTrace (prefixWord ++ tailWord_303028) baseStart_303028 baseEnd_303028 := by
    simpa [prefixWord, tailWord_303028, baseEnd_303028] using wordTrace_append hprefix tailTrace_303028
  have hstable : (prefixWord ++ tailWord_303028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303028).length < 2 ^ (prefixWord ++ tailWord_303028).sum := by decide
  have hdescent : baseEnd_303028 < baseStart_303028 := by decide
  rcases family_descends (prefixWord ++ tailWord_303028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303063 : List Nat := [1, 1, 3, 2, 1, 1, 6, 3, 2]
def baseStart_303063 : Nat := 118140960795 + 303063 * 2 ^ 59
def prefixEnd_303063 : Nat := 4983230072969 + 3 ^ 40 * 303063 * 2
def baseEnd_303063 : Nat := 138326211194358220727773

theorem tailTrace_303063 : CollatzResearch.WordTrace tailWord_303063 prefixEnd_303063 138326211194358220727773 := by
  unfold tailWord_303063
  simp only [CollatzResearch.WordTrace]
  refine ⟨11053615701061984884761843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7369077134041323256507895 11053615701061984884761843)
  ·
    refine ⟨16580423551592977327142765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11053615701061984884761843 16580423551592977327142765)
    ·
      refine ⟨6217658831847366497678537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16580423551592977327142765 6217658831847366497678537)
      ·
        refine ⟨4663244123885524873258903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6217658831847366497678537 4663244123885524873258903)
        ·
          refine ⟨6994866185828287309888355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4663244123885524873258903 6994866185828287309888355)
          ·
            refine ⟨10492299278742430964832533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6994866185828287309888355 10492299278742430964832533)
            ·
              refine ⟨491826528691051451476525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10492299278742430964832533 491826528691051451476525)
              ·
                refine ⟨184434948259144294303697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 491826528691051451476525 184434948259144294303697)
                ·
                  refine ⟨138326211194358220727773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184434948259144294303697 138326211194358220727773)
                  ·
                    rfl

theorem cell20_303063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 3, 2].length) (baseStart_303063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303063 prefixEnd_303063 := by exact prefixLift 303063
  have htrace : WordTrace (prefixWord ++ tailWord_303063) baseStart_303063 baseEnd_303063 := by
    simpa [prefixWord, tailWord_303063, baseEnd_303063] using wordTrace_append hprefix tailTrace_303063
  have hstable : (prefixWord ++ tailWord_303063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303063).length < 2 ^ (prefixWord ++ tailWord_303063).sum := by decide
  have hdescent : baseEnd_303063 < baseStart_303063 := by decide
  rcases family_descends (prefixWord ++ tailWord_303063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303110 : List Nat := [6, 2, 1, 2, 1, 2, 1, 3, 2]
def baseStart_303110 : Nat := 118140960795 + 303110 * 2 ^ 59
def prefixEnd_303110 : Nat := 4983230072969 + 3 ^ 40 * 303110 * 2
def baseEnd_303110 : Nat := 138347663275034946160915

theorem tailTrace_303110 : CollatzResearch.WordTrace tailWord_303110 prefixEnd_303110 138347663275034946160915 := by
  unfold tailWord_303110
  simp only [CollatzResearch.WordTrace]
  refine ⟨345479060371615997241337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7370219954594474607815189 345479060371615997241337)
  ·
    refine ⟨259109295278711997931003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 345479060371615997241337 259109295278711997931003)
    ·
      refine ⟨388663942918067996896505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259109295278711997931003 388663942918067996896505)
      ·
        refine ⟨291497957188550997672379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 388663942918067996896505 291497957188550997672379)
        ·
          refine ⟨437246935782826496508569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291497957188550997672379 437246935782826496508569)
          ·
            refine ⟨327935201837119872381427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 437246935782826496508569 327935201837119872381427)
            ·
              refine ⟨491902802755679808572141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327935201837119872381427 491902802755679808572141)
              ·
                refine ⟨184463551033379928214553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 491902802755679808572141 184463551033379928214553)
                ·
                  refine ⟨138347663275034946160915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184463551033379928214553 138347663275034946160915)
                  ·
                    rfl

theorem cell20_303110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_303110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303110 prefixEnd_303110 := by exact prefixLift 303110
  have htrace : WordTrace (prefixWord ++ tailWord_303110) baseStart_303110 baseEnd_303110 := by
    simpa [prefixWord, tailWord_303110, baseEnd_303110] using wordTrace_append hprefix tailTrace_303110
  have hstable : (prefixWord ++ tailWord_303110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303110).length < 2 ^ (prefixWord ++ tailWord_303110).sum := by decide
  have hdescent : baseEnd_303110 < baseStart_303110 := by decide
  rcases family_descends (prefixWord ++ tailWord_303110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303146 : List Nat := [3, 1, 4, 1, 2, 2, 2, 5]
def baseStart_303146 : Nat := 118140960795 + 303146 * 2 ^ 59
def prefixEnd_303146 : Nat := 4983230072969 + 3 ^ 40 * 303146 * 2
def baseEnd_303146 : Nat := 46121364885326273653589

theorem tailTrace_303146 : CollatzResearch.WordTrace tailWord_303146 prefixEnd_303146 46121364885326273653589 := by
  unfold tailWord_303146
  simp only [CollatzResearch.WordTrace]
  refine ⟨2764160739940322515008323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7371095306507526706688861 2764160739940322515008323)
  ·
    refine ⟨4146241109910483772512485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2764160739940322515008323 4146241109910483772512485)
    ·
      refine ⟨777420208108215707346091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4146241109910483772512485 777420208108215707346091)
      ·
        refine ⟨1166130312162323561019137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 777420208108215707346091 1166130312162323561019137)
        ·
          refine ⟨874597734121742670764353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1166130312162323561019137 874597734121742670764353)
          ·
            refine ⟨655948300591307003073265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 874597734121742670764353 655948300591307003073265)
            ·
              refine ⟨491961225443480252304949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 655948300591307003073265 491961225443480252304949)
              ·
                refine ⟨46121364885326273653589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 491961225443480252304949 46121364885326273653589)
                ·
                  rfl

theorem cell20_303146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_303146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303146 prefixEnd_303146 := by exact prefixLift 303146
  have htrace : WordTrace (prefixWord ++ tailWord_303146) baseStart_303146 baseEnd_303146 := by
    simpa [prefixWord, tailWord_303146, baseEnd_303146] using wordTrace_append hprefix tailTrace_303146
  have hstable : (prefixWord ++ tailWord_303146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303146).length < 2 ^ (prefixWord ++ tailWord_303146).sum := by decide
  have hdescent : baseEnd_303146 < baseStart_303146 := by decide
  rcases family_descends (prefixWord ++ tailWord_303146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303153 : List Nat := [1, 2, 2, 3, 1, 4, 1, 3, 3]
def baseStart_303153 : Nat := 118140960795 + 303153 * 2 ^ 59
def prefixEnd_303153 : Nat := 4983230072969 + 3 ^ 40 * 303153 * 2
def baseEnd_303153 : Nat := 138367289646717907727405

theorem tailTrace_303153 : CollatzResearch.WordTrace tailWord_303153 prefixEnd_303153 138367289646717907727405 := by
  unfold tailWord_303153
  simp only [CollatzResearch.WordTrace]
  refine ⟨11056898270735930255538113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7371265513823953503692075 11056898270735930255538113)
  ·
    refine ⟨8292673703051947691653585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11056898270735930255538113 8292673703051947691653585)
    ·
      refine ⟨6219505277288960768740189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8292673703051947691653585 6219505277288960768740189)
      ·
        refine ⟨2332314478983360288277571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6219505277288960768740189 2332314478983360288277571)
        ·
          refine ⟨3498471718475040432416357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2332314478983360288277571 3498471718475040432416357)
          ·
            refine ⟨655963447214070081078067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3498471718475040432416357 655963447214070081078067)
            ·
              refine ⟨983945170821105121617101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 655963447214070081078067 983945170821105121617101)
              ·
                refine ⟨368979439057914420606413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 983945170821105121617101 368979439057914420606413)
                ·
                  refine ⟨138367289646717907727405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 368979439057914420606413 138367289646717907727405)
                  ·
                    rfl

theorem cell20_303153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 3].length) (baseStart_303153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303153 prefixEnd_303153 := by exact prefixLift 303153
  have htrace : WordTrace (prefixWord ++ tailWord_303153) baseStart_303153 baseEnd_303153 := by
    simpa [prefixWord, tailWord_303153, baseEnd_303153] using wordTrace_append hprefix tailTrace_303153
  have hstable : (prefixWord ++ tailWord_303153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303153).length < 2 ^ (prefixWord ++ tailWord_303153).sum := by decide
  have hdescent : baseEnd_303153 < baseStart_303153 := by decide
  rcases family_descends (prefixWord ++ tailWord_303153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303190 : List Nat := [5, 2, 2, 1, 1, 1, 4, 2, 2]
def baseStart_303190 : Nat := 118140960795 + 303190 * 2 ^ 59
def prefixEnd_303190 : Nat := 4983230072969 + 3 ^ 40 * 303190 * 2
def baseEnd_303190 : Nat := 138384177454910223493921

theorem tailTrace_303190 : CollatzResearch.WordTrace tailWord_303190 prefixEnd_303190 138384177454910223493921 := by
  unfold tailWord_303190
  simp only [CollatzResearch.WordTrace]
  refine ⟨691140485725117848414689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7372165181067923716423349 691140485725117848414689)
  ·
    refine ⟨518355364293838386311017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 691140485725117848414689 518355364293838386311017)
    ·
      refine ⟨388766523220378789733263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 518355364293838386311017 388766523220378789733263)
      ·
        refine ⟨583149784830568184599895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388766523220378789733263 583149784830568184599895)
        ·
          refine ⟨874724677245852276899843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 583149784830568184599895 874724677245852276899843)
          ·
            refine ⟨1312087015868778415349765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 874724677245852276899843 1312087015868778415349765)
            ·
              refine ⟨246016315475395952878081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1312087015868778415349765 246016315475395952878081)
              ·
                refine ⟨184512236606546964658561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246016315475395952878081 184512236606546964658561)
                ·
                  refine ⟨138384177454910223493921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184512236606546964658561 138384177454910223493921)
                  ·
                    rfl

theorem cell20_303190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_303190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303190 prefixEnd_303190 := by exact prefixLift 303190
  have htrace : WordTrace (prefixWord ++ tailWord_303190) baseStart_303190 baseEnd_303190 := by
    simpa [prefixWord, tailWord_303190, baseEnd_303190] using wordTrace_append hprefix tailTrace_303190
  have hstable : (prefixWord ++ tailWord_303190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303190).length < 2 ^ (prefixWord ++ tailWord_303190).sum := by decide
  have hdescent : baseEnd_303190 < baseStart_303190 := by decide
  rcases family_descends (prefixWord ++ tailWord_303190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303205 : List Nat := [1, 3, 1, 3, 2, 2, 3, 5]
def baseStart_303205 : Nat := 118140960795 + 303205 * 2 ^ 59
def prefixEnd_303205 : Nat := 4983230072969 + 3 ^ 40 * 303205 * 2
def baseEnd_303205 : Nat := 46130341287878945997953

theorem tailTrace_303205 : CollatzResearch.WordTrace tailWord_303205 prefixEnd_303205 46130341287878945997953 := by
  unfold tailWord_303205
  simp only [CollatzResearch.WordTrace]
  refine ⟨11058794866547543136431069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7372529911031695424287379 11058794866547543136431069)
  ·
    refine ⟨4147048074955328676161651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11058794866547543136431069 4147048074955328676161651)
    ·
      refine ⟨6220572112432993014242477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4147048074955328676161651 6220572112432993014242477)
      ·
        refine ⟨2332714542162372380340929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6220572112432993014242477 2332714542162372380340929)
        ·
          refine ⟨1749535906621779285255697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2332714542162372380340929 1749535906621779285255697)
          ·
            refine ⟨1312151929966334463941773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1749535906621779285255697 1312151929966334463941773)
            ·
              refine ⟨492056973737375423978165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1312151929966334463941773 492056973737375423978165)
              ·
                refine ⟨46130341287878945997953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 492056973737375423978165 46130341287878945997953)
                ·
                  rfl

theorem cell20_303205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 5].length) (baseStart_303205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303205 prefixEnd_303205 := by exact prefixLift 303205
  have htrace : WordTrace (prefixWord ++ tailWord_303205) baseStart_303205 baseEnd_303205 := by
    simpa [prefixWord, tailWord_303205, baseEnd_303205] using wordTrace_append hprefix tailTrace_303205
  have hstable : (prefixWord ++ tailWord_303205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303205).length < 2 ^ (prefixWord ++ tailWord_303205).sum := by decide
  have hdescent : baseEnd_303205 < baseStart_303205 := by decide
  rcases family_descends (prefixWord ++ tailWord_303205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303277 : List Nat := [1, 5, 2, 1, 2, 3, 2, 4]
def baseStart_303277 : Nat := 118140960795 + 303277 * 2 ^ 59
def prefixEnd_303277 : Nat := 4983230072969 + 3 ^ 40 * 303277 * 2
def baseEnd_303277 : Nat := 46141295541841529197855

theorem tailTrace_303277 : CollatzResearch.WordTrace tailWord_303277 prefixEnd_303277 46141295541841529197855 := by
  unfold tailWord_303277
  simp only [CollatzResearch.WordTrace]
  refine ⟨11061420922286699433052085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7374280614857799622034723 11061420922286699433052085)
  ·
    refine ⟨1037008211464378071848633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11061420922286699433052085 1037008211464378071848633)
    ·
      refine ⟨777756158598283553886475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1037008211464378071848633 777756158598283553886475)
      ·
        refine ⟨1166634237897425330829713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 777756158598283553886475 1166634237897425330829713)
        ·
          refine ⟨874975678423068998122285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1166634237897425330829713 874975678423068998122285)
          ·
            refine ⟨328115879408650874295857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 874975678423068998122285 328115879408650874295857)
            ·
              refine ⟨246086909556488155721893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328115879408650874295857 246086909556488155721893)
              ·
                refine ⟨46141295541841529197855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 246086909556488155721893 46141295541841529197855)
                ·
                  rfl

theorem cell20_303277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 4].length) (baseStart_303277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303277 prefixEnd_303277 := by exact prefixLift 303277
  have htrace : WordTrace (prefixWord ++ tailWord_303277) baseStart_303277 baseEnd_303277 := by
    simpa [prefixWord, tailWord_303277, baseEnd_303277] using wordTrace_append hprefix tailTrace_303277
  have hstable : (prefixWord ++ tailWord_303277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303277).length < 2 ^ (prefixWord ++ tailWord_303277).sum := by decide
  have hdescent : baseEnd_303277 < baseStart_303277 := by decide
  rcases family_descends (prefixWord ++ tailWord_303277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303308 : List Nat := [2, 2, 1, 6, 1, 2, 1, 1, 4]
def baseStart_303308 : Nat := 118140960795 + 303308 * 2 ^ 59
def prefixEnd_303308 : Nat := 4983230072969 + 3 ^ 40 * 303308 * 2
def baseEnd_303308 : Nat := 138438035870226257560105

theorem tailTrace_303308 : CollatzResearch.WordTrace tailWord_303308 prefixEnd_303308 138438035870226257560105 := by
  unfold tailWord_303308
  simp only [CollatzResearch.WordTrace]
  refine ⟨5531275792587195863715289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7375034390116261151620385 5531275792587195863715289)
  ·
    refine ⟨4148456844440396897786467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5531275792587195863715289 4148456844440396897786467)
    ·
      refine ⟨6222685266660595346679701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4148456844440396897786467 6222685266660595346679701)
      ·
        refine ⟨291688371874715406875611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6222685266660595346679701 291688371874715406875611)
        ·
          refine ⟨437532557812073110313417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291688371874715406875611 437532557812073110313417)
          ·
            refine ⟨328149418359054832735063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 437532557812073110313417 328149418359054832735063)
            ·
              refine ⟨492224127538582249102595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328149418359054832735063 492224127538582249102595)
              ·
                refine ⟨738336191307873373653893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 492224127538582249102595 738336191307873373653893)
                ·
                  refine ⟨138438035870226257560105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 738336191307873373653893 138438035870226257560105)
                  ·
                    rfl

theorem cell20_303308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_303308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303308 prefixEnd_303308 := by exact prefixLift 303308
  have htrace : WordTrace (prefixWord ++ tailWord_303308) baseStart_303308 baseEnd_303308 := by
    simpa [prefixWord, tailWord_303308, baseEnd_303308] using wordTrace_append hprefix tailTrace_303308
  have hstable : (prefixWord ++ tailWord_303308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303308).length < 2 ^ (prefixWord ++ tailWord_303308).sum := by decide
  have hdescent : baseEnd_303308 < baseStart_303308 := by decide
  rcases family_descends (prefixWord ++ tailWord_303308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303318 : List Nat := [5, 2, 1, 2, 1, 3, 2, 1, 3]
def baseStart_303318 : Nat := 118140960795 + 303318 * 2 ^ 59
def prefixEnd_303318 : Nat := 4983230072969 + 3 ^ 40 * 303318 * 2
def baseEnd_303318 : Nat := 138442600142710667226731

theorem tailTrace_303318 : CollatzResearch.WordTrace tailWord_303318 prefixEnd_303318 138442600142710667226731 := by
  unfold tailWord_303318
  simp only [CollatzResearch.WordTrace]
  refine ⟨691432269696135214705913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7375277543425442290196405 691432269696135214705913)
  ·
    refine ⟨518574202272101411029435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 691432269696135214705913 518574202272101411029435)
    ·
      refine ⟨777861303408152116544153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 518574202272101411029435 777861303408152116544153)
      ·
        refine ⟨583395977556114087408115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 777861303408152116544153 583395977556114087408115)
        ·
          refine ⟨875093966334171131112173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 583395977556114087408115 875093966334171131112173)
          ·
            refine ⟨328160237375314174167065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 875093966334171131112173 328160237375314174167065)
            ·
              refine ⟨246120178031485630625299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328160237375314174167065 246120178031485630625299)
              ·
                refine ⟨369180267047228445937949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246120178031485630625299 369180267047228445937949)
                ·
                  refine ⟨138442600142710667226731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 369180267047228445937949 138442600142710667226731)
                  ·
                    rfl

theorem cell20_303318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_303318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303318 prefixEnd_303318 := by exact prefixLift 303318
  have htrace : WordTrace (prefixWord ++ tailWord_303318) baseStart_303318 baseEnd_303318 := by
    simpa [prefixWord, tailWord_303318, baseEnd_303318] using wordTrace_append hprefix tailTrace_303318
  have hstable : (prefixWord ++ tailWord_303318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303318).length < 2 ^ (prefixWord ++ tailWord_303318).sum := by decide
  have hdescent : baseEnd_303318 < baseStart_303318 := by decide
  rcases family_descends (prefixWord ++ tailWord_303318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303340 : List Nat := [2, 2, 1, 1, 2, 3, 1, 8]
def baseStart_303340 : Nat := 118140960795 + 303340 * 2 ^ 59
def prefixEnd_303340 : Nat := 4983230072969 + 3 ^ 40 * 303340 * 2
def baseEnd_303340 : Nat := 46150880514058789497769

theorem tailTrace_303340 : CollatzResearch.WordTrace tailWord_303340 prefixEnd_303340 46150880514058789497769 := by
  unfold tailWord_303340
  simp only [CollatzResearch.WordTrace]
  refine ⟨5531859360529230596297737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7375812480705640795063649 5531859360529230596297737)
  ·
    refine ⟨4148894520396922947223303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5531859360529230596297737 4148894520396922947223303)
    ·
      refine ⟨6223341780595384420834955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4148894520396922947223303 6223341780595384420834955)
      ·
        refine ⟨9335012670893076631252433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6223341780595384420834955 9335012670893076631252433)
        ·
          refine ⟨7001259503169807473439325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9335012670893076631252433 7001259503169807473439325)
          ·
            refine ⟨2625472313688677802539747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7001259503169807473439325 2625472313688677802539747)
            ·
              refine ⟨3938208470533016703809621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2625472313688677802539747 3938208470533016703809621)
              ·
                refine ⟨46150880514058789497769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3938208470533016703809621 46150880514058789497769)
                ·
                  rfl

theorem cell20_303340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 8].length) (baseStart_303340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303340 prefixEnd_303340 := by exact prefixLift 303340
  have htrace : WordTrace (prefixWord ++ tailWord_303340) baseStart_303340 baseEnd_303340 := by
    simpa [prefixWord, tailWord_303340, baseEnd_303340] using wordTrace_append hprefix tailTrace_303340
  have hstable : (prefixWord ++ tailWord_303340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303340).length < 2 ^ (prefixWord ++ tailWord_303340).sum := by decide
  have hdescent : baseEnd_303340 < baseStart_303340 := by decide
  rcases family_descends (prefixWord ++ tailWord_303340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303371 : List Nat := [1, 1, 1, 1, 5, 2, 2, 3, 4]
def baseStart_303371 : Nat := 118140960795 + 303371 * 2 ^ 59
def prefixEnd_303371 : Nat := 4983230072969 + 3 ^ 40 * 303371 * 2
def baseEnd_303371 : Nat := 138466790786878038459847

theorem tailTrace_303371 : CollatzResearch.WordTrace tailWord_303371 prefixEnd_303371 138466790786878038459847 := by
  unfold tailWord_303371
  simp only [CollatzResearch.WordTrace]
  refine ⟨11064849383946153486973967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7376566255964102324649311 11064849383946153486973967)
  ·
    refine ⟨16597274075919230230460951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11064849383946153486973967 16597274075919230230460951)
    ·
      refine ⟨24895911113878845345691427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16597274075919230230460951 24895911113878845345691427)
      ·
        refine ⟨37343866670818268018537141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24895911113878845345691427 37343866670818268018537141)
        ·
          refine ⟨3500987500389212626737857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37343866670818268018537141 3500987500389212626737857)
          ·
            refine ⟨2625740625291909470053393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3500987500389212626737857 2625740625291909470053393)
            ·
              refine ⟨1969305468968932102540045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2625740625291909470053393 1969305468968932102540045)
              ·
                refine ⟨738489550863349538452517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1969305468968932102540045 738489550863349538452517)
                ·
                  refine ⟨138466790786878038459847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 738489550863349538452517 138466790786878038459847)
                  ·
                    rfl

theorem cell20_303371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 4].length) (baseStart_303371 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303371 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303371 prefixEnd_303371 := by exact prefixLift 303371
  have htrace : WordTrace (prefixWord ++ tailWord_303371) baseStart_303371 baseEnd_303371 := by
    simpa [prefixWord, tailWord_303371, baseEnd_303371] using wordTrace_append hprefix tailTrace_303371
  have hstable : (prefixWord ++ tailWord_303371).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303371).length < 2 ^ (prefixWord ++ tailWord_303371).sum := by decide
  have hdescent : baseEnd_303371 < baseStart_303371 := by decide
  rcases family_descends (prefixWord ++ tailWord_303371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303395 : List Nat := [1, 1, 1, 4, 2, 2, 5, 4]
def baseStart_303395 : Nat := 118140960795 + 303395 * 2 ^ 59
def prefixEnd_303395 : Nat := 4983230072969 + 3 ^ 40 * 303395 * 2
def baseEnd_303395 : Nat := 46159248346946873886583

theorem tailTrace_303395 : CollatzResearch.WordTrace tailWord_303395 prefixEnd_303395 46159248346946873886583 := by
  unfold tailWord_303395
  simp only [CollatzResearch.WordTrace]
  refine ⟨11065724735859205585847639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7377149823906137057231759 11065724735859205585847639)
  ·
    refine ⟨16598587103788808378771459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11065724735859205585847639 16598587103788808378771459)
    ·
      refine ⟨24897880655683212568157189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16598587103788808378771459 24897880655683212568157189)
      ·
        refine ⟨4668352622940602356529473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24897880655683212568157189 4668352622940602356529473)
        ·
          refine ⟨3501264467205451767397105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4668352622940602356529473 3501264467205451767397105)
          ·
            refine ⟨2625948350404088825547829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3501264467205451767397105 2625948350404088825547829)
            ·
              refine ⟨246182657850383327395109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2625948350404088825547829 246182657850383327395109)
              ·
                refine ⟨46159248346946873886583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 246182657850383327395109 46159248346946873886583)
                ·
                  rfl

theorem cell20_303395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 4].length) (baseStart_303395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303395 prefixEnd_303395 := by exact prefixLift 303395
  have htrace : WordTrace (prefixWord ++ tailWord_303395) baseStart_303395 baseEnd_303395 := by
    simpa [prefixWord, tailWord_303395, baseEnd_303395] using wordTrace_append hprefix tailTrace_303395
  have hstable : (prefixWord ++ tailWord_303395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303395).length < 2 ^ (prefixWord ++ tailWord_303395).sum := by decide
  have hdescent : baseEnd_303395 < baseStart_303395 := by decide
  rcases family_descends (prefixWord ++ tailWord_303395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303447 : List Nat := [1, 1, 3, 2, 3, 1, 1, 4, 4]
def baseStart_303447 : Nat := 118140960795 + 303447 * 2 ^ 59
def prefixEnd_303447 : Nat := 4983230072969 + 3 ^ 40 * 303447 * 2
def baseEnd_303447 : Nat := 138501479257759551926203

theorem tailTrace_303447 : CollatzResearch.WordTrace tailWord_303447 prefixEnd_303447 138501479257759551926203 := by
  unfold tailWord_303447
  simp only [CollatzResearch.WordTrace]
  refine ⟨11067621331670818466740595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7378414221113878977827063 11067621331670818466740595)
  ·
    refine ⟨16601431997506227700110893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11067621331670818466740595 16601431997506227700110893)
    ·
      refine ⟨6225536999064835387541585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16601431997506227700110893 6225536999064835387541585)
      ·
        refine ⟨4669152749298626540656189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6225536999064835387541585 4669152749298626540656189)
        ·
          refine ⟨1750932280986984952746071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4669152749298626540656189 1750932280986984952746071)
          ·
            refine ⟨2626398421480477429119107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1750932280986984952746071 2626398421480477429119107)
            ·
              refine ⟨3939597632220716143678661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2626398421480477429119107 3939597632220716143678661)
              ·
                refine ⟨738674556041384276939749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3939597632220716143678661 738674556041384276939749)
                ·
                  refine ⟨138501479257759551926203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 738674556041384276939749 138501479257759551926203)
                  ·
                    rfl

theorem cell20_303447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 4].length) (baseStart_303447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303447 prefixEnd_303447 := by exact prefixLift 303447
  have htrace : WordTrace (prefixWord ++ tailWord_303447) baseStart_303447 baseEnd_303447 := by
    simpa [prefixWord, tailWord_303447, baseEnd_303447] using wordTrace_append hprefix tailTrace_303447
  have hstable : (prefixWord ++ tailWord_303447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303447).length < 2 ^ (prefixWord ++ tailWord_303447).sum := by decide
  have hdescent : baseEnd_303447 < baseStart_303447 := by decide
  rcases family_descends (prefixWord ++ tailWord_303447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303491 : List Nat := [1, 1, 1, 3, 7, 1, 2, 1, 3]
def baseStart_303491 : Nat := 118140960795 + 303491 * 2 ^ 59
def prefixEnd_303491 : Nat := 4983230072969 + 3 ^ 40 * 303491 * 2
def baseEnd_303491 : Nat := 138521562056690954459357

theorem tailTrace_303491 : CollatzResearch.WordTrace tailWord_303491 prefixEnd_303491 138521562056690954459357 := by
  unfold tailWord_303491
  simp only [CollatzResearch.WordTrace]
  refine ⟨11069226143511413981342327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7379484095674275987561551 11069226143511413981342327)
  ·
    refine ⟨16603839215267120972013491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11069226143511413981342327 16603839215267120972013491)
    ·
      refine ⟨24905758822900681458020237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16603839215267120972013491 24905758822900681458020237)
      ·
        refine ⟨9339659558587755546757589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24905758822900681458020237 9339659558587755546757589)
        ·
          refine ⟨218898270904400520627131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 9339659558587755546757589 218898270904400520627131)
          ·
            refine ⟨328347406356600780940697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218898270904400520627131 328347406356600780940697)
            ·
              refine ⟨246260554767450585705523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328347406356600780940697 246260554767450585705523)
              ·
                refine ⟨369390832151175878558285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246260554767450585705523 369390832151175878558285)
                ·
                  refine ⟨138521562056690954459357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 369390832151175878558285 138521562056690954459357)
                  ·
                    rfl

theorem cell20_303491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 3].length) (baseStart_303491 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303491 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303491 prefixEnd_303491 := by exact prefixLift 303491
  have htrace : WordTrace (prefixWord ++ tailWord_303491) baseStart_303491 baseEnd_303491 := by
    simpa [prefixWord, tailWord_303491, baseEnd_303491] using wordTrace_append hprefix tailTrace_303491
  have hstable : (prefixWord ++ tailWord_303491).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303491).length < 2 ^ (prefixWord ++ tailWord_303491).sum := by decide
  have hdescent : baseEnd_303491 < baseStart_303491 := by decide
  rcases family_descends (prefixWord ++ tailWord_303491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303564 : List Nat := [2, 2, 1, 4, 3, 1, 3, 4]
def baseStart_303564 : Nat := 118140960795 + 303564 * 2 ^ 59
def prefixEnd_303564 : Nat := 4983230072969 + 3 ^ 40 * 303564 * 2
def baseEnd_303564 : Nat := 46184960415275715008575

theorem tailTrace_303564 : CollatzResearch.WordTrace tailWord_303564 prefixEnd_303564 46184960415275715008575 := by
  unfold tailWord_303564
  simp only [CollatzResearch.WordTrace]
  refine ⟨5535944336123473724374873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7381259114831298299166497 5535944336123473724374873)
  ·
    refine ⟨4151958252092605293281155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5535944336123473724374873 4151958252092605293281155)
    ·
      refine ⟨6227937378138907939921733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4151958252092605293281155 6227937378138907939921733)
      ·
        refine ⟨1167738258401045238735325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6227937378138907939921733 1167738258401045238735325)
        ·
          refine ⟨437901846900391964525747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1167738258401045238735325 437901846900391964525747)
          ·
            refine ⟨656852770350587946788621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437901846900391964525747 656852770350587946788621)
            ·
              refine ⟨246319788881470480045733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 656852770350587946788621 246319788881470480045733)
              ·
                refine ⟨46184960415275715008575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 246319788881470480045733 46184960415275715008575)
                ·
                  rfl

theorem cell20_303564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 4].length) (baseStart_303564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303564 prefixEnd_303564 := by exact prefixLift 303564
  have htrace : WordTrace (prefixWord ++ tailWord_303564) baseStart_303564 baseEnd_303564 := by
    simpa [prefixWord, tailWord_303564, baseEnd_303564] using wordTrace_append hprefix tailTrace_303564
  have hstable : (prefixWord ++ tailWord_303564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303564).length < 2 ^ (prefixWord ++ tailWord_303564).sum := by decide
  have hdescent : baseEnd_303564 < baseStart_303564 := by decide
  rcases family_descends (prefixWord ++ tailWord_303564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303574 : List Nat := [5, 2, 1, 1, 1, 1, 4, 3, 2]
def baseStart_303574 : Nat := 118140960795 + 303574 * 2 ^ 59
def prefixEnd_303574 : Nat := 4983230072969 + 3 ^ 40 * 303574 * 2
def baseEnd_303574 : Nat := 138559445518311554692351

theorem tailTrace_303574 : CollatzResearch.WordTrace tailWord_303574 prefixEnd_303574 138559445518311554692351 := by
  unfold tailWord_303574
  simp only [CollatzResearch.WordTrace]
  refine ⟨692015837638169947288361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7381502268140479437742517 692015837638169947288361)
  ·
    refine ⟨519011878228627460466271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 692015837638169947288361 519011878228627460466271)
    ·
      refine ⟨778517817342941190699407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 519011878228627460466271 778517817342941190699407)
      ·
        refine ⟨1167776726014411786049111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 778517817342941190699407 1167776726014411786049111)
        ·
          refine ⟨1751665089021617679073667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1167776726014411786049111 1751665089021617679073667)
          ·
            refine ⟨2627497633532426518610501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1751665089021617679073667 2627497633532426518610501)
            ·
              refine ⟨492655806287329972239469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2627497633532426518610501 492655806287329972239469)
              ·
                refine ⟨184745927357748739589801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 492655806287329972239469 184745927357748739589801)
                ·
                  refine ⟨138559445518311554692351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184745927357748739589801 138559445518311554692351)
                  ·
                    rfl

theorem cell20_303574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_303574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303574 prefixEnd_303574 := by exact prefixLift 303574
  have htrace : WordTrace (prefixWord ++ tailWord_303574) baseStart_303574 baseEnd_303574 := by
    simpa [prefixWord, tailWord_303574, baseEnd_303574] using wordTrace_append hprefix tailTrace_303574
  have hstable : (prefixWord ++ tailWord_303574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303574).length < 2 ^ (prefixWord ++ tailWord_303574).sum := by decide
  have hdescent : baseEnd_303574 < baseStart_303574 := by decide
  rcases family_descends (prefixWord ++ tailWord_303574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303592 : List Nat := [2, 1, 4, 1, 1, 4, 1, 1, 5]
def baseStart_303592 : Nat := 118140960795 + 303592 * 2 ^ 59
def prefixEnd_303592 : Nat := 4983230072969 + 3 ^ 40 * 303592 * 2
def baseEnd_303592 : Nat := 138567661208783492092277

theorem tailTrace_303592 : CollatzResearch.WordTrace tailWord_303592 prefixEnd_303592 138567661208783492092277 := by
  unfold tailWord_303592
  simp only [CollatzResearch.WordTrace]
  refine ⟨5536454958072754115384515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7381939944097005487179353 5536454958072754115384515)
  ·
    refine ⟨8304682437109131173076773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5536454958072754115384515 8304682437109131173076773)
    ·
      refine ⟨1557127956957962094951895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8304682437109131173076773 1557127956957962094951895)
      ·
        refine ⟨2335691935436943142427843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1557127956957962094951895 2335691935436943142427843)
        ·
          refine ⟨3503537903155414713641765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2335691935436943142427843 3503537903155414713641765)
          ·
            refine ⟨656913356841640258807831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3503537903155414713641765 656913356841640258807831)
            ·
              refine ⟨985370035262460388211747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 656913356841640258807831 985370035262460388211747)
              ·
                refine ⟨1478055052893690582317621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 985370035262460388211747 1478055052893690582317621)
                ·
                  refine ⟨138567661208783492092277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1478055052893690582317621 138567661208783492092277)
                  ·
                    rfl

theorem cell20_303592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_303592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303592 prefixEnd_303592 := by exact prefixLift 303592
  have htrace : WordTrace (prefixWord ++ tailWord_303592) baseStart_303592 baseEnd_303592 := by
    simpa [prefixWord, tailWord_303592, baseEnd_303592] using wordTrace_append hprefix tailTrace_303592
  have hstable : (prefixWord ++ tailWord_303592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303592).length < 2 ^ (prefixWord ++ tailWord_303592).sum := by decide
  have hdescent : baseEnd_303592 < baseStart_303592 := by decide
  rcases family_descends (prefixWord ++ tailWord_303592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303605 : List Nat := [1, 3, 5, 1, 2, 1, 3, 1, 3]
def baseStart_303605 : Nat := 118140960795 + 303605 * 2 ^ 59
def prefixEnd_303605 : Nat := 4983230072969 + 3 ^ 40 * 303605 * 2
def baseEnd_303605 : Nat := 138573594763013224658891

theorem tailTrace_303605 : CollatzResearch.WordTrace tailWord_303605 prefixEnd_303605 138573594763013224658891 := by
  unfold tailWord_303605
  simp only [CollatzResearch.WordTrace]
  refine ⟨11073384065098411450992269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7382256043398940967328179 11073384065098411450992269)
  ·
    refine ⟨4152519024411904294122101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11073384065098411450992269 4152519024411904294122101)
    ·
      refine ⟨389298658538616027573947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4152519024411904294122101 389298658538616027573947)
      ·
        refine ⟨583947987807924041360921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389298658538616027573947 583947987807924041360921)
        ·
          refine ⟨437960990855943031020691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 583947987807924041360921 437960990855943031020691)
          ·
            refine ⟨656941486283914546531037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437960990855943031020691 656941486283914546531037)
            ·
              refine ⟨246353057356467954949139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 656941486283914546531037 246353057356467954949139)
              ·
                refine ⟨369529586034701932423709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246353057356467954949139 369529586034701932423709)
                ·
                  refine ⟨138573594763013224658891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 369529586034701932423709 138573594763013224658891)
                  ·
                    rfl

theorem cell20_303605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_303605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303605 prefixEnd_303605 := by exact prefixLift 303605
  have htrace : WordTrace (prefixWord ++ tailWord_303605) baseStart_303605 baseEnd_303605 := by
    simpa [prefixWord, tailWord_303605, baseEnd_303605] using wordTrace_append hprefix tailTrace_303605
  have hstable : (prefixWord ++ tailWord_303605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303605).length < 2 ^ (prefixWord ++ tailWord_303605).sum := by decide
  have hdescent : baseEnd_303605 < baseStart_303605 := by decide
  rcases family_descends (prefixWord ++ tailWord_303605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303623 : List Nat := [1, 1, 4, 3, 3, 1, 1, 6]
def baseStart_303623 : Nat := 118140960795 + 303623 * 2 ^ 59
def prefixEnd_303623 : Nat := 4983230072969 + 3 ^ 40 * 303623 * 2
def baseEnd_303623 : Nat := 46193936817828387352939

theorem tailTrace_303623 : CollatzResearch.WordTrace tailWord_303623 prefixEnd_303623 46193936817828387352939 := by
  unfold tailWord_303623
  simp only [CollatzResearch.WordTrace]
  refine ⟨11074040579033200525147523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7382693719355467016765015 11074040579033200525147523)
  ·
    refine ⟨16611060868549800787721285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11074040579033200525147523 16611060868549800787721285)
    ·
      refine ⟨3114573912853087647697741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16611060868549800787721285 3114573912853087647697741)
      ·
        refine ⟨1167965217319907867886653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3114573912853087647697741 1167965217319907867886653)
        ·
          refine ⟨437986956494965450457495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1167965217319907867886653 437986956494965450457495)
          ·
            refine ⟨656980434742448175686243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437986956494965450457495 656980434742448175686243)
            ·
              refine ⟨985470652113672263529365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 656980434742448175686243 985470652113672263529365)
              ·
                refine ⟨46193936817828387352939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 985470652113672263529365 46193936817828387352939)
                ·
                  rfl

theorem cell20_303623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 6].length) (baseStart_303623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303623 prefixEnd_303623 := by exact prefixLift 303623
  have htrace : WordTrace (prefixWord ++ tailWord_303623) baseStart_303623 baseEnd_303623 := by
    simpa [prefixWord, tailWord_303623, baseEnd_303623] using wordTrace_append hprefix tailTrace_303623
  have hstable : (prefixWord ++ tailWord_303623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303623).length < 2 ^ (prefixWord ++ tailWord_303623).sum := by decide
  have hdescent : baseEnd_303623 < baseStart_303623 := by decide
  rcases family_descends (prefixWord ++ tailWord_303623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303629 : List Nat := [1, 7, 1, 1, 1, 1, 3, 3, 2]
def baseStart_303629 : Nat := 118140960795 + 303629 * 2 ^ 59
def prefixEnd_303629 : Nat := 4983230072969 + 3 ^ 40 * 303629 * 2
def baseEnd_303629 : Nat := 138584549016975807858793

theorem tailTrace_303629 : CollatzResearch.WordTrace tailWord_303629 prefixEnd_303629 138584549016975807858793 := by
  unfold tailWord_303629
  simp only [CollatzResearch.WordTrace]
  refine ⟨11074259417011463549865941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7382839611340975699910627 11074259417011463549865941)
  ·
    refine ⟨259552955086206176949983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 11074259417011463549865941 259552955086206176949983)
    ·
      refine ⟨389329432629309265424975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259552955086206176949983 389329432629309265424975)
      ·
        refine ⟨583994148943963898137463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389329432629309265424975 583994148943963898137463)
        ·
          refine ⟨875991223415945847206195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 583994148943963898137463 875991223415945847206195)
          ·
            refine ⟨1313986835123918770809293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 875991223415945847206195 1313986835123918770809293)
            ·
              refine ⟨492745063171469539053485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1313986835123918770809293 492745063171469539053485)
              ·
                refine ⟨184779398689301077145057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 492745063171469539053485 184779398689301077145057)
                ·
                  refine ⟨138584549016975807858793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184779398689301077145057 138584549016975807858793)
                  ·
                    rfl

theorem cell20_303629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_303629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303629 prefixEnd_303629 := by exact prefixLift 303629
  have htrace : WordTrace (prefixWord ++ tailWord_303629) baseStart_303629 baseEnd_303629 := by
    simpa [prefixWord, tailWord_303629, baseEnd_303629] using wordTrace_append hprefix tailTrace_303629
  have hstable : (prefixWord ++ tailWord_303629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303629).length < 2 ^ (prefixWord ++ tailWord_303629).sum := by decide
  have hdescent : baseEnd_303629 < baseStart_303629 := by decide
  rcases family_descends (prefixWord ++ tailWord_303629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303630 : List Nat := [4, 1, 1, 2, 3, 1, 1, 2, 5]
def baseStart_303630 : Nat := 118140960795 + 303630 * 2 ^ 59
def prefixEnd_303630 : Nat := 4983230072969 + 3 ^ 40 * 303630 * 2
def baseEnd_303630 : Nat := 138585005444224248825455

theorem tailTrace_303630 : CollatzResearch.WordTrace tailWord_303630 prefixEnd_303630 138585005444224248825455 := by
  unfold tailWord_303630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1384286986250980090081543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7382863926671893813768229 1384286986250980090081543)
  ·
    refine ⟨2076430479376470135122315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1384286986250980090081543 2076430479376470135122315)
    ·
      refine ⟨3114645719064705202683473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2076430479376470135122315 3114645719064705202683473)
      ·
        refine ⟨2335984289298528902012605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3114645719064705202683473 2335984289298528902012605)
        ·
          refine ⟨875994108486948338254727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2335984289298528902012605 875994108486948338254727)
          ·
            refine ⟨1313991162730422507382091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 875994108486948338254727 1313991162730422507382091)
            ·
              refine ⟨1970986744095633761073137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1313991162730422507382091 1970986744095633761073137)
              ·
                refine ⟨1478240058071725320804853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1970986744095633761073137 1478240058071725320804853)
                ·
                  refine ⟨138585005444224248825455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1478240058071725320804853 138585005444224248825455)
                  ·
                    rfl

theorem cell20_303630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_303630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303630 prefixEnd_303630 := by exact prefixLift 303630
  have htrace : WordTrace (prefixWord ++ tailWord_303630) baseStart_303630 baseEnd_303630 := by
    simpa [prefixWord, tailWord_303630, baseEnd_303630] using wordTrace_append hprefix tailTrace_303630
  have hstable : (prefixWord ++ tailWord_303630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303630).length < 2 ^ (prefixWord ++ tailWord_303630).sum := by decide
  have hdescent : baseEnd_303630 < baseStart_303630 := by decide
  rcases family_descends (prefixWord ++ tailWord_303630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303644 : List Nat := [2, 2, 3, 1, 2, 2, 8]
def baseStart_303644 : Nat := 118140960795 + 303644 * 2 ^ 59
def prefixEnd_303644 : Nat := 4983230072969 + 3 ^ 40 * 303644 * 2
def baseEnd_303644 : Nat := 15399043936189158039859

theorem tailTrace_303644 : CollatzResearch.WordTrace tailWord_303644 prefixEnd_303644 15399043936189158039859 := by
  unfold tailWord_303644
  simp only [CollatzResearch.WordTrace]
  refine ⟨5537403255978560555830993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7383204341304747407774657 5537403255978560555830993)
  ·
    refine ⟨4153052441983920416873245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5537403255978560555830993 4153052441983920416873245)
    ·
      refine ⟨1557394665743970156327467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4153052441983920416873245 1557394665743970156327467)
      ·
        refine ⟨2336091998615955234491201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1557394665743970156327467 2336091998615955234491201)
        ·
          refine ⟨1752068998961966425868401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2336091998615955234491201 1752068998961966425868401)
          ·
            refine ⟨1314051749221474819401301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1752068998961966425868401 1314051749221474819401301)
            ·
              refine ⟨15399043936189158039859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1314051749221474819401301 15399043936189158039859)
              ·
                rfl

theorem cell20_303644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 8].length) (baseStart_303644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303644 prefixEnd_303644 := by exact prefixLift 303644
  have htrace : WordTrace (prefixWord ++ tailWord_303644) baseStart_303644 baseEnd_303644 := by
    simpa [prefixWord, tailWord_303644, baseEnd_303644] using wordTrace_append hprefix tailTrace_303644
  have hstable : (prefixWord ++ tailWord_303644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303644).length < 2 ^ (prefixWord ++ tailWord_303644).sum := by decide
  have hdescent : baseEnd_303644 < baseStart_303644 := by decide
  rcases family_descends (prefixWord ++ tailWord_303644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303692 : List Nat := [2, 2, 1, 3, 1, 2, 2, 5, 2]
def baseStart_303692 : Nat := 118140960795 + 303692 * 2 ^ 59
def prefixEnd_303692 : Nat := 4983230072969 + 3 ^ 40 * 303692 * 2
def baseEnd_303692 : Nat := 138613303933627588758535

theorem tailTrace_303692 : CollatzResearch.WordTrace tailWord_303692 prefixEnd_303692 138613303933627588758535 := by
  unfold tailWord_303692
  simp only [CollatzResearch.WordTrace]
  refine ⟨5538278607891612654704665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7384371477188816872939553 5538278607891612654704665)
  ·
    refine ⟨4153708955918709491028499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5538278607891612654704665 4153708955918709491028499)
    ·
      refine ⟨6230563433878064236542749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4153708955918709491028499 6230563433878064236542749)
      ·
        refine ⟨2336461287704274088703531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6230563433878064236542749 2336461287704274088703531)
        ·
          refine ⟨3504691931556411133055297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2336461287704274088703531 3504691931556411133055297)
          ·
            refine ⟨2628518948667308349791473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3504691931556411133055297 2628518948667308349791473)
            ·
              refine ⟨1971389211500481262343605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2628518948667308349791473 1971389211500481262343605)
              ·
                refine ⟨184817738578170118344713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1971389211500481262343605 184817738578170118344713)
                ·
                  refine ⟨138613303933627588758535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184817738578170118344713 138613303933627588758535)
                  ·
                    rfl

theorem cell20_303692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 5, 2].length) (baseStart_303692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303692 prefixEnd_303692 := by exact prefixLift 303692
  have htrace : WordTrace (prefixWord ++ tailWord_303692) baseStart_303692 baseEnd_303692 := by
    simpa [prefixWord, tailWord_303692, baseEnd_303692] using wordTrace_append hprefix tailTrace_303692
  have hstable : (prefixWord ++ tailWord_303692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303692).length < 2 ^ (prefixWord ++ tailWord_303692).sum := by decide
  have hdescent : baseEnd_303692 < baseStart_303692 := by decide
  rcases family_descends (prefixWord ++ tailWord_303692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303696 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 8]
def baseStart_303696 : Nat := 118140960795 + 303696 * 2 ^ 59
def prefixEnd_303696 : Nat := 4983230072969 + 3 ^ 40 * 303696 * 2
def baseEnd_303696 : Nat := 138615129642621352625185

theorem tailTrace_303696 : CollatzResearch.WordTrace tailWord_303696 prefixEnd_303696 138615129642621352625185 := by
  unfold tailWord_303696
  simp only [CollatzResearch.WordTrace]
  refine ⟨5538351553884366996277471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7384468738512489328369961 5538351553884366996277471)
  ·
    refine ⟨8307527330826550494416207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5538351553884366996277471 8307527330826550494416207)
    ·
      refine ⟨12461290996239825741624311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8307527330826550494416207 12461290996239825741624311)
      ·
        refine ⟨18691936494359738612436467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12461290996239825741624311 18691936494359738612436467)
        ·
          refine ⟨28037904741539607918654701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18691936494359738612436467 28037904741539607918654701)
          ·
            refine ⟨10514214278077352969495513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28037904741539607918654701 10514214278077352969495513)
            ·
              refine ⟨7885660708558014727121635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10514214278077352969495513 7885660708558014727121635)
              ·
                refine ⟨11828491062837022090682453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7885660708558014727121635 11828491062837022090682453)
                ·
                  refine ⟨138615129642621352625185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11828491062837022090682453 138615129642621352625185)
                  ·
                    rfl

theorem cell20_303696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_303696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303696 prefixEnd_303696 := by exact prefixLift 303696
  have htrace : WordTrace (prefixWord ++ tailWord_303696) baseStart_303696 baseEnd_303696 := by
    simpa [prefixWord, tailWord_303696, baseEnd_303696] using wordTrace_append hprefix tailTrace_303696
  have hstable : (prefixWord ++ tailWord_303696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303696).length < 2 ^ (prefixWord ++ tailWord_303696).sum := by decide
  have hdescent : baseEnd_303696 < baseStart_303696 := by decide
  rcases family_descends (prefixWord ++ tailWord_303696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303730 : List Nat := [3, 2, 1, 2, 4, 1, 1, 2, 4]
def baseStart_303730 : Nat := 118140960795 + 303730 * 2 ^ 59
def prefixEnd_303730 : Nat := 4983230072969 + 3 ^ 40 * 303730 * 2
def baseEnd_303730 : Nat := 138630648169068345491713

theorem tailTrace_303730 : CollatzResearch.WordTrace tailWord_303730 prefixEnd_303730 138630648169068345491713 := by
  unfold tailWord_303730
  simp only [CollatzResearch.WordTrace]
  refine ⟨2769485797411389449823161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7385295459763705199528429 2769485797411389449823161)
  ·
    refine ⟨2077114348058542087367371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2769485797411389449823161 2077114348058542087367371)
    ·
      refine ⟨3115671522087813131051057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2077114348058542087367371 3115671522087813131051057)
      ·
        refine ⟨2336753641565859848288293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3115671522087813131051057 2336753641565859848288293)
        ·
          refine ⟨438141307793598721554055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2336753641565859848288293 438141307793598721554055)
          ·
            refine ⟨657211961690398082331083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438141307793598721554055 657211961690398082331083)
            ·
              refine ⟨985817942535597123496625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 657211961690398082331083 985817942535597123496625)
              ·
                refine ⟨739363456901697842622469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 985817942535597123496625 739363456901697842622469)
                ·
                  refine ⟨138630648169068345491713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 739363456901697842622469 138630648169068345491713)
                  ·
                    rfl

theorem cell20_303730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_303730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303730 prefixEnd_303730 := by exact prefixLift 303730
  have htrace : WordTrace (prefixWord ++ tailWord_303730) baseStart_303730 baseEnd_303730 := by
    simpa [prefixWord, tailWord_303730, baseEnd_303730] using wordTrace_append hprefix tailTrace_303730
  have hstable : (prefixWord ++ tailWord_303730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303730).length < 2 ^ (prefixWord ++ tailWord_303730).sum := by decide
  have hdescent : baseEnd_303730 < baseStart_303730 := by decide
  rcases family_descends (prefixWord ++ tailWord_303730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303737 : List Nat := [1, 2, 1, 3, 3, 3, 3, 4]
def baseStart_303737 : Nat := 118140960795 + 303737 * 2 ^ 59
def prefixEnd_303737 : Nat := 4983230072969 + 3 ^ 40 * 303737 * 2
def baseEnd_303737 : Nat := 46211281053269144086117

theorem tailTrace_303737 : CollatzResearch.WordTrace tailWord_303737 prefixEnd_303737 46211281053269144086117 := by
  unfold tailWord_303737
  simp only [CollatzResearch.WordTrace]
  refine ⟨11078198500620197994797465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7385465667080131996531643 11078198500620197994797465)
  ·
    refine ⟨8308648875465148496098099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11078198500620197994797465 8308648875465148496098099)
    ·
      refine ⟨12462973313197722744147149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8308648875465148496098099 12462973313197722744147149)
      ·
        refine ⟨4673614992449146029055181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12462973313197722744147149 4673614992449146029055181)
        ·
          refine ⟨1752605622168429760895693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4673614992449146029055181 1752605622168429760895693)
          ·
            refine ⟨657227108313161160335885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1752605622168429760895693 657227108313161160335885)
            ·
              refine ⟨246460165617435435125957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 657227108313161160335885 246460165617435435125957)
              ·
                refine ⟨46211281053269144086117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 246460165617435435125957 46211281053269144086117)
                ·
                  rfl

theorem cell20_303737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 4].length) (baseStart_303737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303737 prefixEnd_303737 := by exact prefixLift 303737
  have htrace : WordTrace (prefixWord ++ tailWord_303737) baseStart_303737 baseEnd_303737 := by
    simpa [prefixWord, tailWord_303737, baseEnd_303737] using wordTrace_append hprefix tailTrace_303737
  have hstable : (prefixWord ++ tailWord_303737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303737).length < 2 ^ (prefixWord ++ tailWord_303737).sum := by decide
  have hdescent : baseEnd_303737 < baseStart_303737 := by decide
  rcases family_descends (prefixWord ++ tailWord_303737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303758 : List Nat := [4, 1, 1, 3, 1, 1, 9]
def baseStart_303758 : Nat := 118140960795 + 303758 * 2 ^ 59
def prefixEnd_303758 : Nat := 4983230072969 + 3 ^ 40 * 303758 * 2
def baseEnd_303758 : Nat := 15404825348002743617585

theorem tailTrace_303758 : CollatzResearch.WordTrace tailWord_303758 prefixEnd_303758 15404825348002743617585 := by
  unfold tailWord_303758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1384870554193014822663991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7385976289029412387541285 1384870554193014822663991)
  ·
    refine ⟨2077305831289522233995987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1384870554193014822663991 2077305831289522233995987)
    ·
      refine ⟨3115958746934283350993981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2077305831289522233995987 3115958746934283350993981)
      ·
        refine ⟨1168484530100356256622743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3115958746934283350993981 1168484530100356256622743)
        ·
          refine ⟨1752726795150534384934115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1168484530100356256622743 1752726795150534384934115)
          ·
            refine ⟨2629090192725801577401173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1752726795150534384934115 2629090192725801577401173)
            ·
              refine ⟨15404825348002743617585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2629090192725801577401173 15404825348002743617585)
              ·
                rfl

theorem cell20_303758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 9].length) (baseStart_303758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303758 prefixEnd_303758 := by exact prefixLift 303758
  have htrace : WordTrace (prefixWord ++ tailWord_303758) baseStart_303758 baseEnd_303758 := by
    simpa [prefixWord, tailWord_303758, baseEnd_303758] using wordTrace_append hprefix tailTrace_303758
  have hstable : (prefixWord ++ tailWord_303758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303758).length < 2 ^ (prefixWord ++ tailWord_303758).sum := by decide
  have hdescent : baseEnd_303758 < baseStart_303758 := by decide
  rcases family_descends (prefixWord ++ tailWord_303758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303768 : List Nat := [2, 1, 2, 4, 1, 1, 1, 6, 2]
def baseStart_303768 : Nat := 118140960795 + 303768 * 2 ^ 59
def prefixEnd_303768 : Nat := 4983230072969 + 3 ^ 40 * 303768 * 2
def baseEnd_303768 : Nat := 138647992404509102224891

theorem tailTrace_303768 : CollatzResearch.WordTrace tailWord_303768 prefixEnd_303768 138647992404509102224891 := by
  unfold tailWord_303768
  simp only [CollatzResearch.WordTrace]
  refine ⟨5539664581753945144587979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7386219442338593526117305 5539664581753945144587979)
  ·
    refine ⟨8309496872630917716881969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5539664581753945144587979 8309496872630917716881969)
    ·
      refine ⟨6232122654473188287661477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8309496872630917716881969 6232122654473188287661477)
      ·
        refine ⟨1168522997713722803936527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6232122654473188287661477 1168522997713722803936527)
        ·
          refine ⟨1752784496570584205904791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1168522997713722803936527 1752784496570584205904791)
          ·
            refine ⟨2629176744855876308857187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1752784496570584205904791 2629176744855876308857187)
            ·
              refine ⟨3943765117283814463285781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2629176744855876308857187 3943765117283814463285781)
              ·
                refine ⟨184863989872678802966521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3943765117283814463285781 184863989872678802966521)
                ·
                  refine ⟨138647992404509102224891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184863989872678802966521 138647992404509102224891)
                  ·
                    rfl

theorem cell20_303768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 6, 2].length) (baseStart_303768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303768 prefixEnd_303768 := by exact prefixLift 303768
  have htrace : WordTrace (prefixWord ++ tailWord_303768) baseStart_303768 baseEnd_303768 := by
    simpa [prefixWord, tailWord_303768, baseEnd_303768] using wordTrace_append hprefix tailTrace_303768
  have hstable : (prefixWord ++ tailWord_303768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303768).length < 2 ^ (prefixWord ++ tailWord_303768).sum := by decide
  have hdescent : baseEnd_303768 < baseStart_303768 := by decide
  rcases family_descends (prefixWord ++ tailWord_303768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303798 : List Nat := [5, 1, 3, 1, 3, 1, 1, 3, 2]
def baseStart_303798 : Nat := 118140960795 + 303798 * 2 ^ 59
def prefixEnd_303798 : Nat := 4983230072969 + 3 ^ 40 * 303798 * 2
def baseEnd_303798 : Nat := 138661685221962331224769

theorem tailTrace_303798 : CollatzResearch.WordTrace tailWord_303798 prefixEnd_303798 138661685221962331224769 := by
  unfold tailWord_303798
  simp only [CollatzResearch.WordTrace]
  refine ⟨692526459587450338298003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7386948902266136941845365 692526459587450338298003)
  ·
    refine ⟨1038789689381175507447005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 692526459587450338298003 1038789689381175507447005)
    ·
      refine ⟨389546133517940815292627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1038789689381175507447005 389546133517940815292627)
      ·
        refine ⟨584319200276911222938941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389546133517940815292627 584319200276911222938941)
        ·
          refine ⟨219119700103841708602103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 584319200276911222938941 219119700103841708602103)
          ·
            refine ⟨328679550155762562903155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219119700103841708602103 328679550155762562903155)
            ·
              refine ⟨493019325233643844354733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328679550155762562903155 493019325233643844354733)
              ·
                refine ⟨184882246962616441633025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 493019325233643844354733 184882246962616441633025)
                ·
                  refine ⟨138661685221962331224769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184882246962616441633025 138661685221962331224769)
                  ·
                    rfl

theorem cell20_303798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_303798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303798 prefixEnd_303798 := by exact prefixLift 303798
  have htrace : WordTrace (prefixWord ++ tailWord_303798) baseStart_303798 baseEnd_303798 := by
    simpa [prefixWord, tailWord_303798, baseEnd_303798] using wordTrace_append hprefix tailTrace_303798
  have hstable : (prefixWord ++ tailWord_303798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303798).length < 2 ^ (prefixWord ++ tailWord_303798).sum := by decide
  have hdescent : baseEnd_303798 < baseStart_303798 := by decide
  rcases family_descends (prefixWord ++ tailWord_303798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303809 : List Nat := [1, 2, 6, 2, 2, 1, 6]
def baseStart_303809 : Nat := 118140960795 + 303809 * 2 ^ 59
def prefixEnd_303809 : Nat := 4983230072969 + 3 ^ 40 * 303809 * 2
def baseEnd_303809 : Nat := 15407411769077242428673

theorem tailTrace_303809 : CollatzResearch.WordTrace tailWord_303809 prefixEnd_303809 15407411769077242428673 := by
  unfold tailWord_303809
  simp only [CollatzResearch.WordTrace]
  refine ⟨11080824556359354291418481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7387216370906236194278987 11080824556359354291418481)
  ·
    refine ⟨8310618417269515718563861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11080824556359354291418481 8310618417269515718563861)
    ·
      refine ⟨389560238309508549307681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8310618417269515718563861 389560238309508549307681)
      ·
        refine ⟨292170178732131411980761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 389560238309508549307681 292170178732131411980761)
        ·
          refine ⟨219127634049098558985571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292170178732131411980761 219127634049098558985571)
          ·
            refine ⟨328691451073647838478357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219127634049098558985571 328691451073647838478357)
            ·
              refine ⟨15407411769077242428673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 328691451073647838478357 15407411769077242428673)
              ·
                rfl

theorem cell20_303809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 6].length) (baseStart_303809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303809 prefixEnd_303809 := by exact prefixLift 303809
  have htrace : WordTrace (prefixWord ++ tailWord_303809) baseStart_303809 baseEnd_303809 := by
    simpa [prefixWord, tailWord_303809, baseEnd_303809] using wordTrace_append hprefix tailTrace_303809
  have hstable : (prefixWord ++ tailWord_303809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303809).length < 2 ^ (prefixWord ++ tailWord_303809).sum := by decide
  have hdescent : baseEnd_303809 < baseStart_303809 := by decide
  rcases family_descends (prefixWord ++ tailWord_303809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303820 : List Nat := [2, 2, 1, 5, 1, 1, 2, 1, 5]
def baseStart_303820 : Nat := 118140960795 + 303820 * 2 ^ 59
def prefixEnd_303820 : Nat := 4983230072969 + 3 ^ 40 * 303820 * 2
def baseEnd_303820 : Nat := 138671726621428032491345

theorem tailTrace_303820 : CollatzResearch.WordTrace tailWord_303820 prefixEnd_303820 138671726621428032491345 := by
  unfold tailWord_303820
  simp only [CollatzResearch.WordTrace]
  refine ⟨5540612879659751585034457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7387483839546335446712609 5540612879659751585034457)
  ·
    refine ⟨4155459659744813688775843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5540612879659751585034457 4155459659744813688775843)
    ·
      refine ⟨6233189489617220533163765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4155459659744813688775843 6233189489617220533163765)
      ·
        refine ⟨584361514651614424984103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6233189489617220533163765 584361514651614424984103)
        ·
          refine ⟨876542271977421637476155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 584361514651614424984103 876542271977421637476155)
          ·
            refine ⟨1314813407966132456214233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 876542271977421637476155 1314813407966132456214233)
            ·
              refine ⟨986110055974599342160675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1314813407966132456214233 986110055974599342160675)
              ·
                refine ⟨1479165083961899013241013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986110055974599342160675 1479165083961899013241013)
                ·
                  refine ⟨138671726621428032491345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1479165083961899013241013 138671726621428032491345)
                  ·
                    rfl

theorem cell20_303820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_303820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303820 prefixEnd_303820 := by exact prefixLift 303820
  have htrace : WordTrace (prefixWord ++ tailWord_303820) baseStart_303820 baseEnd_303820 := by
    simpa [prefixWord, tailWord_303820, baseEnd_303820] using wordTrace_append hprefix tailTrace_303820
  have hstable : (prefixWord ++ tailWord_303820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303820).length < 2 ^ (prefixWord ++ tailWord_303820).sum := by decide
  have hdescent : baseEnd_303820 < baseStart_303820 := by decide
  rcases family_descends (prefixWord ++ tailWord_303820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303834 : List Nat := [3, 1, 1, 2, 2, 2, 4, 5]
def baseStart_303834 : Nat := 118140960795 + 303834 * 2 ^ 59
def prefixEnd_303834 : Nat := 4983230072969 + 3 ^ 40 * 303834 * 2
def baseEnd_303834 : Nat := 46226038867635402008207

theorem tailTrace_303834 : CollatzResearch.WordTrace tailWord_303834 prefixEnd_303834 46226038867635402008207 := by
  unfold tailWord_303834
  simp only [CollatzResearch.WordTrace]
  refine ⟨2770434095317195890269639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7387824254179189040719037 2770434095317195890269639)
  ·
    refine ⟨4155651142975793835404459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2770434095317195890269639 4155651142975793835404459)
    ·
      refine ⟨6233476714463690753106689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4155651142975793835404459 6233476714463690753106689)
      ·
        refine ⟨4675107535847768064830017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6233476714463690753106689 4675107535847768064830017)
        ·
          refine ⟨3506330651885826048622513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4675107535847768064830017 3506330651885826048622513)
          ·
            refine ⟨2629747988914369536466885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3506330651885826048622513 2629747988914369536466885)
            ·
              refine ⟨493077747921444288087541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2629747988914369536466885 493077747921444288087541)
              ·
                refine ⟨46226038867635402008207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 493077747921444288087541 46226038867635402008207)
                ·
                  rfl

theorem cell20_303834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_303834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303834 prefixEnd_303834 := by exact prefixLift 303834
  have htrace : WordTrace (prefixWord ++ tailWord_303834) baseStart_303834 baseEnd_303834 := by
    simpa [prefixWord, tailWord_303834, baseEnd_303834] using wordTrace_append hprefix tailTrace_303834
  have hstable : (prefixWord ++ tailWord_303834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303834).length < 2 ^ (prefixWord ++ tailWord_303834).sum := by decide
  have hdescent : baseEnd_303834 < baseStart_303834 := by decide
  rcases family_descends (prefixWord ++ tailWord_303834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303882 : List Nat := [3, 1, 2, 2, 1, 2, 3, 4, 2]
def baseStart_303882 : Nat := 118140960795 + 303882 * 2 ^ 59
def prefixEnd_303882 : Nat := 4983230072969 + 3 ^ 40 * 303882 * 2
def baseEnd_303882 : Nat := 138700025110831372424425

theorem tailTrace_303882 : CollatzResearch.WordTrace tailWord_303882 prefixEnd_303882 138700025110831372424425 := by
  unfold tailWord_303882
  simp only [CollatzResearch.WordTrace]
  refine ⟨2770871771273721939706475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7388991390063258505883933 2770871771273721939706475)
  ·
    refine ⟨4156307656910582909559713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2770871771273721939706475 4156307656910582909559713)
    ·
      refine ⟨3117230742682937182169785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4156307656910582909559713 3117230742682937182169785)
      ·
        refine ⟨2337923057012202886627339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3117230742682937182169785 2337923057012202886627339)
        ·
          refine ⟨3506884585518304329941009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2337923057012202886627339 3506884585518304329941009)
          ·
            refine ⟨2630163439138728247455757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3506884585518304329941009 2630163439138728247455757)
            ·
              refine ⟨986311289677023092795909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2630163439138728247455757 986311289677023092795909)
              ·
                refine ⟨184933366814441829899233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 986311289677023092795909 184933366814441829899233)
                ·
                  refine ⟨138700025110831372424425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184933366814441829899233 138700025110831372424425)
                  ·
                    rfl

theorem cell20_303882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 4, 2].length) (baseStart_303882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303882 prefixEnd_303882 := by exact prefixLift 303882
  have htrace : WordTrace (prefixWord ++ tailWord_303882) baseStart_303882 baseEnd_303882 := by
    simpa [prefixWord, tailWord_303882, baseEnd_303882] using wordTrace_append hprefix tailTrace_303882
  have hstable : (prefixWord ++ tailWord_303882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303882).length < 2 ^ (prefixWord ++ tailWord_303882).sum := by decide
  have hdescent : baseEnd_303882 < baseStart_303882 := by decide
  rcases family_descends (prefixWord ++ tailWord_303882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303903 : List Nat := [1, 1, 2, 4, 2, 3, 1, 2, 4]
def baseStart_303903 : Nat := 118140960795 + 303903 * 2 ^ 59
def prefixEnd_303903 : Nat := 4983230072969 + 3 ^ 40 * 303903 * 2
def baseEnd_303903 : Nat := 138709610083048632724339

theorem tailTrace_303903 : CollatzResearch.WordTrace tailWord_303903 prefixEnd_303903 138709610083048632724339 := by
  unfold tailWord_303903
  simp only [CollatzResearch.WordTrace]
  refine ⟨11084253018018808345340363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7389502012012538896893575 11084253018018808345340363)
  ·
    refine ⟨16626379527028212518010545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11084253018018808345340363 16626379527028212518010545)
    ·
      refine ⟨12469784645271159388507909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16626379527028212518010545 12469784645271159388507909)
      ·
        refine ⟨2338084620988342385345233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12469784645271159388507909 2338084620988342385345233)
        ·
          refine ⟨1753563465741256789008925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2338084620988342385345233 1753563465741256789008925)
          ·
            refine ⟨657586299652971295878347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1753563465741256789008925 657586299652971295878347)
            ·
              refine ⟨986379449479456943817521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 657586299652971295878347 986379449479456943817521)
              ·
                refine ⟨739784587109592707863141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 986379449479456943817521 739784587109592707863141)
                ·
                  refine ⟨138709610083048632724339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 739784587109592707863141 138709610083048632724339)
                  ·
                    rfl

theorem cell20_303903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 4].length) (baseStart_303903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303903 prefixEnd_303903 := by exact prefixLift 303903
  have htrace : WordTrace (prefixWord ++ tailWord_303903) baseStart_303903 baseEnd_303903 := by
    simpa [prefixWord, tailWord_303903, baseEnd_303903] using wordTrace_append hprefix tailTrace_303903
  have hstable : (prefixWord ++ tailWord_303903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303903).length < 2 ^ (prefixWord ++ tailWord_303903).sum := by decide
  have hdescent : baseEnd_303903 < baseStart_303903 := by decide
  rcases family_descends (prefixWord ++ tailWord_303903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303930 : List Nat := [3, 1, 1, 1, 7, 1, 1, 2, 3]
def baseStart_303930 : Nat := 118140960795 + 303930 * 2 ^ 59
def prefixEnd_303930 : Nat := 4983230072969 + 3 ^ 40 * 303930 * 2
def baseEnd_303930 : Nat := 138721933618756538824229

theorem tailTrace_303930 : CollatzResearch.WordTrace tailWord_303930 prefixEnd_303930 138721933618756538824229 := by
  unfold tailWord_303930
  simp only [CollatzResearch.WordTrace]
  refine ⟨2771309447230247989143311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7390158525947327971048829 2771309447230247989143311)
  ·
    refine ⟨4156964170845371983714967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2771309447230247989143311 4156964170845371983714967)
    ·
      refine ⟨6235446256268057975572451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4156964170845371983714967 6235446256268057975572451)
      ·
        refine ⟨9353169384402086963358677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6235446256268057975572451 9353169384402086963358677)
        ·
          refine ⟨219214907446923913203719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 9353169384402086963358677 219214907446923913203719)
          ·
            refine ⟨328822361170385869805579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219214907446923913203719 328822361170385869805579)
            ·
              refine ⟨493233541755578804708369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328822361170385869805579 493233541755578804708369)
              ·
                refine ⟨369925156316684103531277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 493233541755578804708369 369925156316684103531277)
                ·
                  refine ⟨138721933618756538824229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 369925156316684103531277 138721933618756538824229)
                  ·
                    rfl

theorem cell20_303930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 3].length) (baseStart_303930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303930 prefixEnd_303930 := by exact prefixLift 303930
  have htrace : WordTrace (prefixWord ++ tailWord_303930) baseStart_303930 baseEnd_303930 := by
    simpa [prefixWord, tailWord_303930, baseEnd_303930] using wordTrace_append hprefix tailTrace_303930
  have hstable : (prefixWord ++ tailWord_303930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303930).length < 2 ^ (prefixWord ++ tailWord_303930).sum := by decide
  have hdescent : baseEnd_303930 < baseStart_303930 := by decide
  rcases family_descends (prefixWord ++ tailWord_303930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303937 : List Nat := [1, 2, 5, 3, 1, 1, 2, 1, 4]
def baseStart_303937 : Nat := 118140960795 + 303937 * 2 ^ 59
def prefixEnd_303937 : Nat := 4983230072969 + 3 ^ 40 * 303937 * 2
def baseEnd_303937 : Nat := 138725128609495625590867

theorem tailTrace_303937 : CollatzResearch.WordTrace tailWord_303937 prefixEnd_303937 138725128609495625590867 := by
  unfold tailWord_303937
  simp only [CollatzResearch.WordTrace]
  refine ⟨11085493099895632152078065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7390328733263754768052043 11085493099895632152078065)
  ·
    refine ⟨8314119824921724114058549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11085493099895632152078065 8314119824921724114058549)
    ·
      refine ⟨779448733586411635692989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8314119824921724114058549 779448733586411635692989)
      ·
        refine ⟨292293275094904363384871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 779448733586411635692989 292293275094904363384871)
        ·
          refine ⟨438439912642356545077307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292293275094904363384871 438439912642356545077307)
          ·
            refine ⟨657659868963534817615961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438439912642356545077307 657659868963534817615961)
            ·
              refine ⟨493244901722651113211971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 657659868963534817615961 493244901722651113211971)
              ·
                refine ⟨739867352583976669817957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 493244901722651113211971 739867352583976669817957)
                ·
                  refine ⟨138725128609495625590867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 739867352583976669817957 138725128609495625590867)
                  ·
                    rfl

theorem cell20_303937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 4].length) (baseStart_303937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303937 prefixEnd_303937 := by exact prefixLift 303937
  have htrace : WordTrace (prefixWord ++ tailWord_303937) baseStart_303937 baseEnd_303937 := by
    simpa [prefixWord, tailWord_303937, baseEnd_303937] using wordTrace_append hprefix tailTrace_303937
  have hstable : (prefixWord ++ tailWord_303937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303937).length < 2 ^ (prefixWord ++ tailWord_303937).sum := by decide
  have hdescent : baseEnd_303937 < baseStart_303937 := by decide
  rcases family_descends (prefixWord ++ tailWord_303937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303955 : List Nat := [1, 1, 1, 2, 1, 1, 3, 7, 3]
def baseStart_303955 : Nat := 118140960795 + 303955 * 2 ^ 59
def prefixEnd_303955 : Nat := 4983230072969 + 3 ^ 40 * 303955 * 2
def baseEnd_303955 : Nat := 138733344299967562990793

theorem tailTrace_303955 : CollatzResearch.WordTrace tailWord_303955 prefixEnd_303955 138733344299967562990793 := by
  unfold tailWord_303955
  simp only [CollatzResearch.WordTrace]
  refine ⟨11086149613830421226233319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7390766409220280817488879 11086149613830421226233319)
  ·
    refine ⟨16629224420745631839349979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11086149613830421226233319 16629224420745631839349979)
    ·
      refine ⟨24943836631118447759024969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16629224420745631839349979 24943836631118447759024969)
      ·
        refine ⟨18707877473338835819268727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24943836631118447759024969 18707877473338835819268727)
        ·
          refine ⟨28061816210008253728903091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18707877473338835819268727 28061816210008253728903091)
          ·
            refine ⟨42092724315012380593354637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28061816210008253728903091 42092724315012380593354637)
            ·
              refine ⟨15784771618129642722507989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42092724315012380593354637 15784771618129642722507989)
              ·
                refine ⟨369955584799913501308781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15784771618129642722507989 369955584799913501308781)
                ·
                  refine ⟨138733344299967562990793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 369955584799913501308781 138733344299967562990793)
                  ·
                    rfl

theorem cell20_303955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 3].length) (baseStart_303955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303955 prefixEnd_303955 := by exact prefixLift 303955
  have htrace : WordTrace (prefixWord ++ tailWord_303955) baseStart_303955 baseEnd_303955 := by
    simpa [prefixWord, tailWord_303955, baseEnd_303955] using wordTrace_append hprefix tailTrace_303955
  have hstable : (prefixWord ++ tailWord_303955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303955).length < 2 ^ (prefixWord ++ tailWord_303955).sum := by decide
  have hdescent : baseEnd_303955 < baseStart_303955 := by decide
  rcases family_descends (prefixWord ++ tailWord_303955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303975 : List Nat := [1, 1, 5, 1, 2, 4, 1, 3, 2]
def baseStart_303975 : Nat := 118140960795 + 303975 * 2 ^ 59
def prefixEnd_303975 : Nat := 4983230072969 + 3 ^ 40 * 303975 * 2
def baseEnd_303975 : Nat := 138742472844936382324045

theorem tailTrace_303975 : CollatzResearch.WordTrace tailWord_303975 prefixEnd_303975 138742472844936382324045 := by
  unfold tailWord_303975
  simp only [CollatzResearch.WordTrace]
  refine ⟨11086879073757964641961379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7391252715838643094640919 11086879073757964641961379)
  ·
    refine ⟨16630318610636946962942069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11086879073757964641961379 16630318610636946962942069)
    ·
      refine ⟨1559092369747213777775819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16630318610636946962942069 1559092369747213777775819)
      ·
        refine ⟨2338638554620820666663729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1559092369747213777775819 2338638554620820666663729)
        ·
          refine ⟨1753978915965615499997797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2338638554620820666663729 1753978915965615499997797)
          ·
            refine ⟨328871046743552906249587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1753978915965615499997797 328871046743552906249587)
            ·
              refine ⟨493306570115329359374381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328871046743552906249587 493306570115329359374381)
              ·
                refine ⟨184989963793248509765393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 493306570115329359374381 184989963793248509765393)
                ·
                  refine ⟨138742472844936382324045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184989963793248509765393 138742472844936382324045)
                  ·
                    rfl

theorem cell20_303975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 3, 2].length) (baseStart_303975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303975 prefixEnd_303975 := by exact prefixLift 303975
  have htrace : WordTrace (prefixWord ++ tailWord_303975) baseStart_303975 baseEnd_303975 := by
    simpa [prefixWord, tailWord_303975, baseEnd_303975] using wordTrace_append hprefix tailTrace_303975
  have hstable : (prefixWord ++ tailWord_303975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303975).length < 2 ^ (prefixWord ++ tailWord_303975).sum := by decide
  have hdescent : baseEnd_303975 < baseStart_303975 := by decide
  rcases family_descends (prefixWord ++ tailWord_303975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303982 : List Nat := [4, 1, 2, 3, 3, 1, 6]
def baseStart_303982 : Nat := 118140960795 + 303982 * 2 ^ 59
def prefixEnd_303982 : Nat := 4983230072969 + 3 ^ 40 * 303982 * 2
def baseEnd_303982 : Nat := 15416185315075052121187

theorem tailTrace_303982 : CollatzResearch.WordTrace tailWord_303982 prefixEnd_303982 15416185315075052121187 := by
  unfold tailWord_303982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1385891798091575604683275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7391422923155069891644133 1385891798091575604683275)
  ·
    refine ⟨2078837697137363407024913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1385891798091575604683275 2078837697137363407024913)
    ·
      refine ⟨1559128272853022555268685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2078837697137363407024913 1559128272853022555268685)
      ·
        refine ⟨584673102319883458225757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1559128272853022555268685 584673102319883458225757)
        ·
          refine ⟨219252413369956296834659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 584673102319883458225757 219252413369956296834659)
          ·
            refine ⟨328878620054934445251989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219252413369956296834659 328878620054934445251989)
            ·
              refine ⟨15416185315075052121187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 328878620054934445251989 15416185315075052121187)
              ·
                rfl

theorem cell20_303982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 6].length) (baseStart_303982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303982 prefixEnd_303982 := by exact prefixLift 303982
  have htrace : WordTrace (prefixWord ++ tailWord_303982) baseStart_303982 baseEnd_303982 := by
    simpa [prefixWord, tailWord_303982, baseEnd_303982] using wordTrace_append hprefix tailTrace_303982
  have hstable : (prefixWord ++ tailWord_303982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303982).length < 2 ^ (prefixWord ++ tailWord_303982).sum := by decide
  have hdescent : baseEnd_303982 < baseStart_303982 := by decide
  rcases family_descends (prefixWord ++ tailWord_303982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303993 : List Nat := [1, 2, 1, 3, 2, 3, 2, 1, 5]
def baseStart_303993 : Nat := 118140960795 + 303993 * 2 ^ 59
def prefixEnd_303993 : Nat := 4983230072969 + 3 ^ 40 * 303993 * 2
def baseEnd_303993 : Nat := 138750688535408319723971

theorem tailTrace_303993 : CollatzResearch.WordTrace tailWord_303993 prefixEnd_303993 138750688535408319723971 := by
  unfold tailWord_303993
  simp only [CollatzResearch.WordTrace]
  refine ⟨11087535587692753716116633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7391690391795169144077755 11087535587692753716116633)
  ·
    refine ⟨8315651690769565287087475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11087535587692753716116633 8315651690769565287087475)
    ·
      refine ⟨12473477536154347930631213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8315651690769565287087475 12473477536154347930631213)
      ·
        refine ⟨4677554076057880473986705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12473477536154347930631213 4677554076057880473986705)
        ·
          refine ⟨3508165557043410355490029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4677554076057880473986705 3508165557043410355490029)
          ·
            refine ⟨1315562083891278883308761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3508165557043410355490029 1315562083891278883308761)
            ·
              refine ⟨986671562918459162481571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1315562083891278883308761 986671562918459162481571)
              ·
                refine ⟨1480007344377688743722357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986671562918459162481571 1480007344377688743722357)
                ·
                  refine ⟨138750688535408319723971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1480007344377688743722357 138750688535408319723971)
                  ·
                    rfl

theorem cell20_303993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_303993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_303993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_303993 prefixEnd_303993 := by exact prefixLift 303993
  have htrace : WordTrace (prefixWord ++ tailWord_303993) baseStart_303993 baseEnd_303993 := by
    simpa [prefixWord, tailWord_303993, baseEnd_303993] using wordTrace_append hprefix tailTrace_303993
  have hstable : (prefixWord ++ tailWord_303993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303993).length < 2 ^ (prefixWord ++ tailWord_303993).sum := by decide
  have hdescent : baseEnd_303993 < baseStart_303993 := by decide
  rcases family_descends (prefixWord ++ tailWord_303993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304000 : List Nat := [2, 1, 1, 2, 1, 2, 2, 5, 4]
def baseStart_304000 : Nat := 118140960795 + 304000 * 2 ^ 59
def prefixEnd_304000 : Nat := 4983230072969 + 3 ^ 40 * 304000 * 2
def baseEnd_304000 : Nat := 138753883526147406490609

theorem tailTrace_304000 : CollatzResearch.WordTrace tailWord_304000 prefixEnd_304000 138753883526147406490609 := by
  unfold tailWord_304000
  simp only [CollatzResearch.WordTrace]
  refine ⟨5543895449333696955810727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7391860599111595941080969 5543895449333696955810727)
  ·
    refine ⟨8315843174000545433716091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5543895449333696955810727 8315843174000545433716091)
    ·
      refine ⟨12473764761000818150574137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8315843174000545433716091 12473764761000818150574137)
      ·
        refine ⟨9355323570750613612930603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12473764761000818150574137 9355323570750613612930603)
        ·
          refine ⟨14032985356125920419395905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9355323570750613612930603 14032985356125920419395905)
          ·
            refine ⟨10524739017094440314546929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14032985356125920419395905 10524739017094440314546929)
            ·
              refine ⟨7893554262820830235910197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10524739017094440314546929 7893554262820830235910197)
              ·
                refine ⟨740020712139452834616581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7893554262820830235910197 740020712139452834616581)
                ·
                  refine ⟨138753883526147406490609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 740020712139452834616581 138753883526147406490609)
                  ·
                    rfl

theorem cell20_304000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_304000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304000 prefixEnd_304000 := by exact prefixLift 304000
  have htrace : WordTrace (prefixWord ++ tailWord_304000) baseStart_304000 baseEnd_304000 := by
    simpa [prefixWord, tailWord_304000, baseEnd_304000] using wordTrace_append hprefix tailTrace_304000
  have hstable : (prefixWord ++ tailWord_304000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304000).length < 2 ^ (prefixWord ++ tailWord_304000).sum := by decide
  have hdescent : baseEnd_304000 < baseStart_304000 := by decide
  rcases family_descends (prefixWord ++ tailWord_304000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304002 : List Nat := [3, 4, 2, 2, 1, 2, 2, 1, 3]
def baseStart_304002 : Nat := 118140960795 + 304002 * 2 ^ 59
def prefixEnd_304002 : Nat := 4983230072969 + 3 ^ 40 * 304002 * 2
def baseEnd_304002 : Nat := 138754796380644288423935

theorem tailTrace_304002 : CollatzResearch.WordTrace tailWord_304002 prefixEnd_304002 138754796380644288423935 := by
  unfold tailWord_304002
  simp only [CollatzResearch.WordTrace]
  refine ⟨2771965961165037063298565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7391909229773432168796173 2771965961165037063298565)
  ·
    refine ⟨519743617718444449368481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2771965961165037063298565 519743617718444449368481)
    ·
      refine ⟨389807713288833337026361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 519743617718444449368481 389807713288833337026361)
      ·
        refine ⟨292355784966625002769771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 389807713288833337026361 292355784966625002769771)
        ·
          refine ⟨438533677449937504154657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292355784966625002769771 438533677449937504154657)
          ·
            refine ⟨328900258087453128115993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 438533677449937504154657 328900258087453128115993)
            ·
              refine ⟨246675193565589846086995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328900258087453128115993 246675193565589846086995)
              ·
                refine ⟨370012790348384769130493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246675193565589846086995 370012790348384769130493)
                ·
                  refine ⟨138754796380644288423935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 370012790348384769130493 138754796380644288423935)
                  ·
                    rfl

theorem cell20_304002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_304002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304002 prefixEnd_304002 := by exact prefixLift 304002
  have htrace : WordTrace (prefixWord ++ tailWord_304002) baseStart_304002 baseEnd_304002 := by
    simpa [prefixWord, tailWord_304002, baseEnd_304002] using wordTrace_append hprefix tailTrace_304002
  have hstable : (prefixWord ++ tailWord_304002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304002).length < 2 ^ (prefixWord ++ tailWord_304002).sum := by decide
  have hdescent : baseEnd_304002 < baseStart_304002 := by decide
  rcases family_descends (prefixWord ++ tailWord_304002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304054 : List Nat := [5, 1, 4, 1, 1, 2, 1, 5]
def baseStart_304054 : Nat := 118140960795 + 304054 * 2 ^ 59
def prefixEnd_304054 : Nat := 4983230072969 + 3 ^ 40 * 304054 * 2
def baseEnd_304054 : Nat := 46259510199187739563463

theorem tailTrace_304054 : CollatzResearch.WordTrace tailWord_304054 prefixEnd_304054 46259510199187739563463 := by
  unfold tailWord_304054
  simp only [CollatzResearch.WordTrace]
  refine ⟨693110027529485070880451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7393173626981174089391477 693110027529485070880451)
  ·
    refine ⟨1039665041294227606320677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 693110027529485070880451 1039665041294227606320677)
    ·
      refine ⟨194937195242667676185127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1039665041294227606320677 194937195242667676185127)
      ·
        refine ⟨292405792864001514277691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194937195242667676185127 292405792864001514277691)
        ·
          refine ⟨438608689296002271416537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292405792864001514277691 438608689296002271416537)
          ·
            refine ⟨328956516972001703562403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 438608689296002271416537 328956516972001703562403)
            ·
              refine ⟨493434775458002555343605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328956516972001703562403 493434775458002555343605)
              ·
                refine ⟨46259510199187739563463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 493434775458002555343605 46259510199187739563463)
                ·
                  rfl

theorem cell20_304054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_304054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304054 prefixEnd_304054 := by exact prefixLift 304054
  have htrace : WordTrace (prefixWord ++ tailWord_304054) baseStart_304054 baseEnd_304054 := by
    simpa [prefixWord, tailWord_304054, baseEnd_304054] using wordTrace_append hprefix tailTrace_304054
  have hstable : (prefixWord ++ tailWord_304054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304054).length < 2 ^ (prefixWord ++ tailWord_304054).sum := by decide
  have hdescent : baseEnd_304054 < baseStart_304054 := by decide
  rcases family_descends (prefixWord ++ tailWord_304054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304103 : List Nat := [1, 1, 5, 2, 2, 3, 1, 2, 3]
def baseStart_304103 : Nat := 118140960795 + 304103 * 2 ^ 59
def prefixEnd_304103 : Nat := 4983230072969 + 3 ^ 40 * 304103 * 2
def baseEnd_304103 : Nat := 138800895532736826056855

theorem tailTrace_304103 : CollatzResearch.WordTrace tailWord_304103 prefixEnd_304103 138800895532736826056855 := by
  unfold tailWord_304103
  simp only [CollatzResearch.WordTrace]
  refine ⟨11091547617294242502620963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7394365078196161668413975 11091547617294242502620963)
  ·
    refine ⟨16637321425941363753931445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11091547617294242502620963 16637321425941363753931445)
    ·
      refine ⟨1559748883682002851931073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16637321425941363753931445 1559748883682002851931073)
      ·
        refine ⟨1169811662761502138948305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1559748883682002851931073 1169811662761502138948305)
        ·
          refine ⟨877358747071126604211229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1169811662761502138948305 877358747071126604211229)
          ·
            refine ⟨329009530151672476579211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 877358747071126604211229 329009530151672476579211)
            ·
              refine ⟨493514295227508714868817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329009530151672476579211 493514295227508714868817)
              ·
                refine ⟨370135721420631536151613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 493514295227508714868817 370135721420631536151613)
                ·
                  refine ⟨138800895532736826056855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 370135721420631536151613 138800895532736826056855)
                  ·
                    rfl

theorem cell20_304103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 3].length) (baseStart_304103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304103 prefixEnd_304103 := by exact prefixLift 304103
  have htrace : WordTrace (prefixWord ++ tailWord_304103) baseStart_304103 baseEnd_304103 := by
    simpa [prefixWord, tailWord_304103, baseEnd_304103] using wordTrace_append hprefix tailTrace_304103
  have hstable : (prefixWord ++ tailWord_304103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304103).length < 2 ^ (prefixWord ++ tailWord_304103).sum := by decide
  have hdescent : baseEnd_304103 < baseStart_304103 := by decide
  rcases family_descends (prefixWord ++ tailWord_304103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304110 : List Nat := [4, 1, 2, 1, 4, 1, 2, 1, 4]
def baseStart_304110 : Nat := 118140960795 + 304110 * 2 ^ 59
def prefixEnd_304110 : Nat := 4983230072969 + 3 ^ 40 * 304110 * 2
def baseEnd_304110 : Nat := 138804090523475912823493

theorem tailTrace_304110 : CollatzResearch.WordTrace tailWord_304110 prefixEnd_304110 138804090523475912823493 := by
  unfold tailWord_304110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1386475366033610337265723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7394535285512588465417189 1386475366033610337265723)
  ·
    refine ⟨2079713049050415505898585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1386475366033610337265723 2079713049050415505898585)
    ·
      refine ⟨1559784786787811629423939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2079713049050415505898585 1559784786787811629423939)
      ·
        refine ⟨2339677180181717444135909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1559784786787811629423939 2339677180181717444135909)
        ·
          refine ⟨438689471284072020775483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2339677180181717444135909 438689471284072020775483)
          ·
            refine ⟨658034206926108031163225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438689471284072020775483 658034206926108031163225)
            ·
              refine ⟨493525655194581023372419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 658034206926108031163225 493525655194581023372419)
              ·
                refine ⟨740288482791871535058629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 493525655194581023372419 740288482791871535058629)
                ·
                  refine ⟨138804090523475912823493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 740288482791871535058629 138804090523475912823493)
                  ·
                    rfl

theorem cell20_304110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_304110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304110 prefixEnd_304110 := by exact prefixLift 304110
  have htrace : WordTrace (prefixWord ++ tailWord_304110) baseStart_304110 baseEnd_304110 := by
    simpa [prefixWord, tailWord_304110, baseEnd_304110] using wordTrace_append hprefix tailTrace_304110
  have hstable : (prefixWord ++ tailWord_304110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304110).length < 2 ^ (prefixWord ++ tailWord_304110).sum := by decide
  have hdescent : baseEnd_304110 < baseStart_304110 := by decide
  rcases family_descends (prefixWord ++ tailWord_304110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304121 : List Nat := [1, 2, 1, 3, 1, 3, 2, 7]
def baseStart_304121 : Nat := 118140960795 + 304121 * 2 ^ 59
def prefixEnd_304121 : Nat := 4983230072969 + 3 ^ 40 * 304121 * 2
def baseEnd_304121 : Nat := 46269703741069587818927

theorem tailTrace_304121 : CollatzResearch.WordTrace tailWord_304121 prefixEnd_304121 46269703741069587818927 := by
  unfold tailWord_304121
  simp only [CollatzResearch.WordTrace]
  refine ⟨11092204131229031576776217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7394802754152687717850811 11092204131229031576776217)
  ·
    refine ⟨8319153098421773682582163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11092204131229031576776217 8319153098421773682582163)
    ·
      refine ⟨12478729647632660523873245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8319153098421773682582163 12478729647632660523873245)
      ·
        refine ⟨4679523617862247696452467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12478729647632660523873245 4679523617862247696452467)
        ·
          refine ⟨7019285426793371544678701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4679523617862247696452467 7019285426793371544678701)
          ·
            refine ⟨2632232035047514329254513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7019285426793371544678701 2632232035047514329254513)
            ·
              refine ⟨1974174026285635746940885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2632232035047514329254513 1974174026285635746940885)
              ·
                refine ⟨46269703741069587818927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1974174026285635746940885 46269703741069587818927)
                ·
                  rfl

theorem cell20_304121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 7].length) (baseStart_304121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304121 prefixEnd_304121 := by exact prefixLift 304121
  have htrace : WordTrace (prefixWord ++ tailWord_304121) baseStart_304121 baseEnd_304121 := by
    simpa [prefixWord, tailWord_304121, baseEnd_304121] using wordTrace_append hprefix tailTrace_304121
  have hstable : (prefixWord ++ tailWord_304121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304121).length < 2 ^ (prefixWord ++ tailWord_304121).sum := by decide
  have hdescent : baseEnd_304121 < baseStart_304121 := by decide
  rcases family_descends (prefixWord ++ tailWord_304121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
