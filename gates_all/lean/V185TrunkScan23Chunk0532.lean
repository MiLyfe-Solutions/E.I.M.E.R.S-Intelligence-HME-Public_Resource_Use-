import V185TrunkScan23Chunk0531

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3145270 : List Nat := [5, 1, 2, 1, 3, 1, 3, 1, 1, 5]
def baseStart_3145270 : Nat := 118140960795 + 3145270 * 2 ^ 59
def prefixEnd_3145270 : Nat := 4983230072969 + 3 ^ 40 * 3145270 * 2
def baseEnd_3145270 : Nat := 538345099389004783453391

theorem tailTrace_3145270 : CollatzResearch.WordTrace tailWord_3145270 prefixEnd_3145270 538345099389004783453391 := by
  unfold tailWord_3145270
  simp only [CollatzResearch.WordTrace]
  refine ⟨7169838832201964637179579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76478280876820956129915509 7169838832201964637179579)
  ·
    refine ⟨10754758248302946955769369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7169838832201964637179579 10754758248302946955769369)
    ·
      refine ⟨8066068686227210216827027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10754758248302946955769369 8066068686227210216827027)
      ·
        refine ⟨12099103029340815325240541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8066068686227210216827027 12099103029340815325240541)
        ·
          refine ⟨4537163636002805746965203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12099103029340815325240541 4537163636002805746965203)
          ·
            refine ⟨6805745454004208620447805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4537163636002805746965203 6805745454004208620447805)
            ·
              refine ⟨2552154545251578232667927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6805745454004208620447805 2552154545251578232667927)
              ·
                refine ⟨3828231817877367349001891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2552154545251578232667927 3828231817877367349001891)
                ·
                  refine ⟨5742347726816051023502837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3828231817877367349001891 5742347726816051023502837)
                  ·
                    refine ⟨538345099389004783453391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5742347726816051023502837 538345099389004783453391)
                    ·
                      rfl

theorem cell23_3145270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_3145270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145270 prefixEnd_3145270 := by exact prefixLift 3145270
  have htrace : WordTrace (prefixWord ++ tailWord_3145270) baseStart_3145270 baseEnd_3145270 := by
    simpa [prefixWord, tailWord_3145270, baseEnd_3145270] using wordTrace_append hprefix tailTrace_3145270
  have hstable : (prefixWord ++ tailWord_3145270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145270).length < 2 ^ (prefixWord ++ tailWord_3145270).sum := by decide
  have hdescent : baseEnd_3145270 < baseStart_3145270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145273 : List Nat := [1, 2, 1, 5, 1, 3, 3, 1, 1, 1, 4]
def baseStart_3145273 : Nat := 118140960795 + 3145273 * 2 ^ 59
def prefixEnd_3145273 : Nat := 4983230072969 + 3 ^ 40 * 3145273 * 2
def baseEnd_3145273 : Nat := 1615036838608977838622659

theorem tailTrace_3145273 : CollatzResearch.WordTrace tailWord_3145273 prefixEnd_3145273 1615036838608977838622659 := by
  unfold tailWord_3145273
  simp only [CollatzResearch.WordTrace]
  refine ⟨114717530734220565707232473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76478353822813710471488315 114717530734220565707232473)
  ·
    refine ⟨86038148050665424280424355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114717530734220565707232473 86038148050665424280424355)
    ·
      refine ⟨129057222075998136420636533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86038148050665424280424355 129057222075998136420636533)
      ·
        refine ⟨12099114569624825289434675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 129057222075998136420636533 12099114569624825289434675)
        ·
          refine ⟨18148671854437237934152013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12099114569624825289434675 18148671854437237934152013)
          ·
            refine ⟨6805751945413964225307005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18148671854437237934152013 6805751945413964225307005)
            ·
              refine ⟨2552156979530236584490127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6805751945413964225307005 2552156979530236584490127)
              ·
                refine ⟨3828235469295354876735191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2552156979530236584490127 3828235469295354876735191)
                ·
                  refine ⟨5742353203943032315102787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3828235469295354876735191 5742353203943032315102787)
                  ·
                    refine ⟨8613529805914548472654181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5742353203943032315102787 8613529805914548472654181)
                    ·
                      refine ⟨1615036838608977838622659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8613529805914548472654181 1615036838608977838622659)
                      ·
                        rfl

theorem cell23_3145273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_3145273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145273 prefixEnd_3145273 := by exact prefixLift 3145273
  have htrace : WordTrace (prefixWord ++ tailWord_3145273) baseStart_3145273 baseEnd_3145273 := by
    simpa [prefixWord, tailWord_3145273, baseEnd_3145273] using wordTrace_append hprefix tailTrace_3145273
  have hstable : (prefixWord ++ tailWord_3145273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145273).length < 2 ^ (prefixWord ++ tailWord_3145273).sum := by decide
  have hdescent : baseEnd_3145273 < baseStart_3145273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145290 : List Nat := [3, 1, 2, 1, 1, 3, 3, 4, 1, 2, 2]
def baseStart_3145290 : Nat := 118140960795 + 3145290 * 2 ^ 59
def prefixEnd_3145290 : Nat := 4983230072969 + 3 ^ 40 * 3145290 * 2
def baseEnd_3145290 : Nat := 1615045567780104272110081

theorem tailTrace_3145290 : CollatzResearch.WordTrace tailWord_3145290 prefixEnd_3145290 1615045567780104272110081 := by
  unfold tailWord_3145290
  simp only [CollatzResearch.WordTrace]
  refine ⟨28679537693789744402650331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76478767183439318407067549 28679537693789744402650331)
  ·
    refine ⟨43019306540684616603975497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28679537693789744402650331 43019306540684616603975497)
    ·
      refine ⟨32264479905513462452981623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43019306540684616603975497 32264479905513462452981623)
      ·
        refine ⟨48396719858270193679472435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32264479905513462452981623 48396719858270193679472435)
        ·
          refine ⟨72595079787405290519208653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48396719858270193679472435 72595079787405290519208653)
          ·
            refine ⟨27223154920276983944703245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72595079787405290519208653 27223154920276983944703245)
            ·
              refine ⟨10208683095103868979263717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27223154920276983944703245 10208683095103868979263717)
              ·
                refine ⟨1914128080331975433611947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10208683095103868979263717 1914128080331975433611947)
                ·
                  refine ⟨2871192120497963150417921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1914128080331975433611947 2871192120497963150417921)
                  ·
                    refine ⟨2153394090373472362813441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2871192120497963150417921 2153394090373472362813441)
                    ·
                      refine ⟨1615045567780104272110081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2153394090373472362813441 1615045567780104272110081)
                      ·
                        rfl

theorem cell23_3145290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 4, 1, 2, 2].length) (baseStart_3145290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145290 prefixEnd_3145290 := by exact prefixLift 3145290
  have htrace : WordTrace (prefixWord ++ tailWord_3145290) baseStart_3145290 baseEnd_3145290 := by
    simpa [prefixWord, tailWord_3145290, baseEnd_3145290] using wordTrace_append hprefix tailTrace_3145290
  have hstable : (prefixWord ++ tailWord_3145290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145290).length < 2 ^ (prefixWord ++ tailWord_3145290).sum := by decide
  have hdescent : baseEnd_3145290 < baseStart_3145290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145419 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 4]
def baseStart_3145419 : Nat := 118140960795 + 3145419 * 2 ^ 59
def prefixEnd_3145419 : Nat := 4983230072969 + 3 ^ 40 * 3145419 * 2
def baseEnd_3145419 : Nat := 1615111806784534267396987

theorem tailTrace_3145419 : CollatzResearch.WordTrace tailWord_3145419 prefixEnd_3145419 1615111806784534267396987 := by
  unfold tailWord_3145419
  simp only [CollatzResearch.WordTrace]
  refine ⟨114722855791691632642047311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76481903861127755094698207 114722855791691632642047311)
  ·
    refine ⟨172084283687537448963070967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114722855791691632642047311 172084283687537448963070967)
    ·
      refine ⟨258126425531306173444606451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172084283687537448963070967 258126425531306173444606451)
      ·
        refine ⟨387189638296959260166909677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258126425531306173444606451 387189638296959260166909677)
        ·
          refine ⟨145196114361359722562591129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 387189638296959260166909677 145196114361359722562591129)
          ·
            refine ⟨108897085771019791921943347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145196114361359722562591129 108897085771019791921943347)
            ·
              refine ⟨163345628656529687882915021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108897085771019791921943347 163345628656529687882915021)
              ·
                refine ⟨61254610746198632956093133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163345628656529687882915021 61254610746198632956093133)
                ·
                  refine ⟨22970479029824487358534925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61254610746198632956093133 22970479029824487358534925)
                  ·
                    refine ⟨8613929636184182759450597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22970479029824487358534925 8613929636184182759450597)
                    ·
                      refine ⟨1615111806784534267396987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8613929636184182759450597 1615111806784534267396987)
                      ·
                        rfl

theorem cell23_3145419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 4].length) (baseStart_3145419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145419 prefixEnd_3145419 := by exact prefixLift 3145419
  have htrace : WordTrace (prefixWord ++ tailWord_3145419) baseStart_3145419 baseEnd_3145419 := by
    simpa [prefixWord, tailWord_3145419, baseEnd_3145419] using wordTrace_append hprefix tailTrace_3145419
  have hstable : (prefixWord ++ tailWord_3145419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145419).length < 2 ^ (prefixWord ++ tailWord_3145419).sum := by decide
  have hdescent : baseEnd_3145419 < baseStart_3145419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145449 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 2, 1, 6]
def baseStart_3145449 : Nat := 118140960795 + 3145449 * 2 ^ 59
def prefixEnd_3145449 : Nat := 4983230072969 + 3 ^ 40 * 3145449 * 2
def baseEnd_3145449 : Nat := 1615127211204169150021849

theorem tailTrace_3145449 : CollatzResearch.WordTrace tailWord_3145449 prefixEnd_3145449 1615127211204169150021849 := by
  unfold tailWord_3145449
  simp only [CollatzResearch.WordTrace]
  refine ⟨114723949981582947765639401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76482633321055298510426267 114723949981582947765639401)
  ·
    refine ⟨86042962486187210824229551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114723949981582947765639401 86042962486187210824229551)
    ·
      refine ⟨129064443729280816236344327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86042962486187210824229551 129064443729280816236344327)
      ·
        refine ⟨193596665593921224354516491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129064443729280816236344327 193596665593921224354516491)
        ·
          refine ⟨290394998390881836531774737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193596665593921224354516491 290394998390881836531774737)
          ·
            refine ⟨217796248793161377398831053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290394998390881836531774737 217796248793161377398831053)
            ·
              refine ⟨81673593297435516524561645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217796248793161377398831053 81673593297435516524561645)
              ·
                refine ⟨30627597486538318696710617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81673593297435516524561645 30627597486538318696710617)
                ·
                  refine ⟨22970698114903739022532963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30627597486538318696710617 22970698114903739022532963)
                  ·
                    refine ⟨34456047172355608533799445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22970698114903739022532963 34456047172355608533799445)
                    ·
                      refine ⟨1615127211204169150021849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34456047172355608533799445 1615127211204169150021849)
                      ·
                        rfl

theorem cell23_3145449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 1, 6].length) (baseStart_3145449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145449 prefixEnd_3145449 := by exact prefixLift 3145449
  have htrace : WordTrace (prefixWord ++ tailWord_3145449) baseStart_3145449 baseEnd_3145449 := by
    simpa [prefixWord, tailWord_3145449, baseEnd_3145449] using wordTrace_append hprefix tailTrace_3145449
  have hstable : (prefixWord ++ tailWord_3145449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145449).length < 2 ^ (prefixWord ++ tailWord_3145449).sum := by decide
  have hdescent : baseEnd_3145449 < baseStart_3145449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145453 : List Nat := [1, 5, 1, 2, 1, 2, 2, 2, 2, 1, 4]
def baseStart_3145453 : Nat := 118140960795 + 3145453 * 2 ^ 59
def prefixEnd_3145453 : Nat := 4983230072969 + 3 ^ 40 * 3145453 * 2
def baseEnd_3145453 : Nat := 1615129265126787134371831

theorem tailTrace_3145453 : CollatzResearch.WordTrace tailWord_3145453 prefixEnd_3145453 1615129265126787134371831 := by
  unfold tailWord_3145453
  simp only [CollatzResearch.WordTrace]
  refine ⟨114724095873568456448785013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76482730582378970965856675 114724095873568456448785013)
  ·
    refine ⟨10755383988147042792073595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114724095873568456448785013 10755383988147042792073595)
    ·
      refine ⟨16133075982220564188110393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10755383988147042792073595 16133075982220564188110393)
      ·
        refine ⟨12099806986665423141082795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16133075982220564188110393 12099806986665423141082795)
        ·
          refine ⟨18149710479998134711624193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12099806986665423141082795 18149710479998134711624193)
          ·
            refine ⟨13612282859998601033718145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18149710479998134711624193 13612282859998601033718145)
            ·
              refine ⟨10209212144998950775288609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13612282859998601033718145 10209212144998950775288609)
              ·
                refine ⟨7656909108749213081466457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10209212144998950775288609 7656909108749213081466457)
                ·
                  refine ⟨5742681831561909811099843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7656909108749213081466457 5742681831561909811099843)
                  ·
                    refine ⟨8614022747342864716649765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5742681831561909811099843 8614022747342864716649765)
                    ·
                      refine ⟨1615129265126787134371831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8614022747342864716649765 1615129265126787134371831)
                      ·
                        rfl

theorem cell23_3145453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_3145453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145453 prefixEnd_3145453 := by exact prefixLift 3145453
  have htrace : WordTrace (prefixWord ++ tailWord_3145453) baseStart_3145453 baseEnd_3145453 := by
    simpa [prefixWord, tailWord_3145453, baseEnd_3145453] using wordTrace_append hprefix tailTrace_3145453
  have hstable : (prefixWord ++ tailWord_3145453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145453).length < 2 ^ (prefixWord ++ tailWord_3145453).sum := by decide
  have hdescent : baseEnd_3145453 < baseStart_3145453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145456 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 3]
def baseStart_3145456 : Nat := 118140960795 + 3145456 * 2 ^ 59
def prefixEnd_3145456 : Nat := 4983230072969 + 3 ^ 40 * 3145456 * 2
def baseEnd_3145456 : Nat := 1615130805568750622634317

theorem tailTrace_3145456 : CollatzResearch.WordTrace tailWord_3145456 prefixEnd_3145456 1615130805568750622634317 := by
  unfold tailWord_3145456
  simp only [CollatzResearch.WordTrace]
  refine ⟨57362102646278793980572111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76482803528371725307429481 57362102646278793980572111)
  ·
    refine ⟨86043153969418190970858167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57362102646278793980572111 86043153969418190970858167)
    ·
      refine ⟨129064730954127286456287251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86043153969418190970858167 129064730954127286456287251)
      ·
        refine ⟨193597096431190929684430877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129064730954127286456287251 193597096431190929684430877)
        ·
          refine ⟨72598911161696598631661579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193597096431190929684430877 72598911161696598631661579)
          ·
            refine ⟨108898366742544897947492369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72598911161696598631661579 108898366742544897947492369)
            ·
              refine ⟨81673775056908673460619277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108898366742544897947492369 81673775056908673460619277)
              ·
                refine ⟨30627665646340752547732229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81673775056908673460619277 30627665646340752547732229)
                ·
                  refine ⟨5742687308688891102699793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30627665646340752547732229 5742687308688891102699793)
                  ·
                    refine ⟨4307015481516668327024845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5742687308688891102699793 4307015481516668327024845)
                    ·
                      refine ⟨1615130805568750622634317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4307015481516668327024845 1615130805568750622634317)
                      ·
                        rfl

theorem cell23_3145456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 3].length) (baseStart_3145456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145456 prefixEnd_3145456 := by exact prefixLift 3145456
  have htrace : WordTrace (prefixWord ++ tailWord_3145456) baseStart_3145456 baseEnd_3145456 := by
    simpa [prefixWord, tailWord_3145456, baseEnd_3145456] using wordTrace_append hprefix tailTrace_3145456
  have hstable : (prefixWord ++ tailWord_3145456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145456).length < 2 ^ (prefixWord ++ tailWord_3145456).sum := by decide
  have hdescent : baseEnd_3145456 < baseStart_3145456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145459 : List Nat := [1, 1, 1, 2, 2, 3, 2, 3, 8]
def baseStart_3145459 : Nat := 118140960795 + 3145459 * 2 ^ 59
def prefixEnd_3145459 : Nat := 4983230072969 + 3 ^ 40 * 3145459 * 2
def baseEnd_3145459 : Nat := 179459149556746012321867

theorem tailTrace_3145459 : CollatzResearch.WordTrace tailWord_3145459 prefixEnd_3145459 179459149556746012321867 := by
  unfold tailWord_3145459
  simp only [CollatzResearch.WordTrace]
  refine ⟨114724314711546719473503431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76482876474364479649002287 114724314711546719473503431)
  ·
    refine ⟨172086472067320079210255147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114724314711546719473503431 172086472067320079210255147)
    ·
      refine ⟨258129708100980118815382721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172086472067320079210255147 258129708100980118815382721)
      ·
        refine ⟨193597281075735089111537041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258129708100980118815382721 193597281075735089111537041)
        ·
          refine ⟨145197960806801316833652781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193597281075735089111537041 145197960806801316833652781)
          ·
            refine ⟨54449235302550493812619793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145197960806801316833652781 54449235302550493812619793)
            ·
              refine ⟨40836926476912870359464845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54449235302550493812619793 40836926476912870359464845)
              ·
                refine ⟨15313847428842326384799317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40836926476912870359464845 15313847428842326384799317)
                ·
                  refine ⟨179459149556746012321867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15313847428842326384799317 179459149556746012321867)
                  ·
                    rfl

theorem cell23_3145459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 8].length) (baseStart_3145459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145459 prefixEnd_3145459 := by exact prefixLift 3145459
  have htrace : WordTrace (prefixWord ++ tailWord_3145459) baseStart_3145459 baseEnd_3145459 := by
    simpa [prefixWord, tailWord_3145459, baseEnd_3145459] using wordTrace_append hprefix tailTrace_3145459
  have hstable : (prefixWord ++ tailWord_3145459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145459).length < 2 ^ (prefixWord ++ tailWord_3145459).sum := by decide
  have hdescent : baseEnd_3145459 < baseStart_3145459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145460 : List Nat := [2, 6, 1, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_3145460 : Nat := 118140960795 + 3145460 * 2 ^ 59
def prefixEnd_3145460 : Nat := 4983230072969 + 3 ^ 40 * 3145460 * 2
def baseEnd_3145460 : Nat := 1615132859491368606984299

theorem tailTrace_3145460 : CollatzResearch.WordTrace tailWord_3145460 prefixEnd_3145460 1615132859491368606984299 := by
  unfold tailWord_3145460
  simp only [CollatzResearch.WordTrace]
  refine ⟨57362175592271548322144917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76482900789695397762859889 57362175592271548322144917)
  ·
    refine ⟨2688851980887728827600543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57362175592271548322144917 2688851980887728827600543)
    ·
      refine ⟨4033277971331593241400815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2688851980887728827600543 4033277971331593241400815)
      ·
        refine ⟨6049916956997389862101223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4033277971331593241400815 6049916956997389862101223)
        ·
          refine ⟨9074875435496084793151835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6049916956997389862101223 9074875435496084793151835)
          ·
            refine ⟨13612313153244127189727753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9074875435496084793151835 13612313153244127189727753)
            ·
              refine ⟨10209234864933095392295815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13612313153244127189727753 10209234864933095392295815)
              ·
                refine ⟨15313852297399643088443723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10209234864933095392295815 15313852297399643088443723)
                ·
                  refine ⟨22970778446099464632665585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15313852297399643088443723 22970778446099464632665585)
                  ·
                    refine ⟨17228083834574598474499189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22970778446099464632665585 17228083834574598474499189)
                    ·
                      refine ⟨1615132859491368606984299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17228083834574598474499189 1615132859491368606984299)
                      ·
                        rfl

theorem cell23_3145460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_3145460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145460 prefixEnd_3145460 := by exact prefixLift 3145460
  have htrace : WordTrace (prefixWord ++ tailWord_3145460) baseStart_3145460 baseEnd_3145460 := by
    simpa [prefixWord, tailWord_3145460, baseEnd_3145460] using wordTrace_append hprefix tailTrace_3145460
  have hstable : (prefixWord ++ tailWord_3145460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145460).length < 2 ^ (prefixWord ++ tailWord_3145460).sum := by decide
  have hdescent : baseEnd_3145460 < baseStart_3145460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145490 : List Nat := [3, 2, 4, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_3145490 : Nat := 118140960795 + 3145490 * 2 ^ 59
def prefixEnd_3145490 : Nat := 4983230072969 + 3 ^ 40 * 3145490 * 2
def baseEnd_3145490 : Nat := 1615148263911003489609161

theorem tailTrace_3145490 : CollatzResearch.WordTrace tailWord_3145490 prefixEnd_3145490 1615148263911003489609161 := by
  unfold tailWord_3145490
  simp only [CollatzResearch.WordTrace]
  refine ⟨28681361343608602941970481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76483630249622941178587949 28681361343608602941970481)
  ·
    refine ⟨21511021007706452206477861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28681361343608602941970481 21511021007706452206477861)
    ·
      refine ⟨4033316438944959788714599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21511021007706452206477861 4033316438944959788714599)
      ·
        refine ⟨6049974658417439683071899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4033316438944959788714599 6049974658417439683071899)
        ·
          refine ⟨9074961987626159524607849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6049974658417439683071899 9074961987626159524607849)
          ·
            refine ⟨6806221490719619643455887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9074961987626159524607849 6806221490719619643455887)
            ·
              refine ⟨10209332236079429465183831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6806221490719619643455887 10209332236079429465183831)
              ·
                refine ⟨15313998354119144197775747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10209332236079429465183831 15313998354119144197775747)
                ·
                  refine ⟨22970997531178716296663621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15313998354119144197775747 22970997531178716296663621)
                  ·
                    refine ⟨4307062037096009305624429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22970997531178716296663621 4307062037096009305624429)
                    ·
                      refine ⟨1615148263911003489609161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4307062037096009305624429 1615148263911003489609161)
                      ·
                        rfl

theorem cell23_3145490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_3145490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145490 prefixEnd_3145490 := by exact prefixLift 3145490
  have htrace : WordTrace (prefixWord ++ tailWord_3145490) baseStart_3145490 baseEnd_3145490 := by
    simpa [prefixWord, tailWord_3145490, baseEnd_3145490] using wordTrace_append hprefix tailTrace_3145490
  have hstable : (prefixWord ++ tailWord_3145490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145490).length < 2 ^ (prefixWord ++ tailWord_3145490).sum := by decide
  have hdescent : baseEnd_3145490 < baseStart_3145490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145499 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 7]
def baseStart_3145499 : Nat := 118140960795 + 3145499 * 2 ^ 59
def prefixEnd_3145499 : Nat := 4983230072969 + 3 ^ 40 * 3145499 * 2
def baseEnd_3145499 : Nat := 1615152885236893954396619

theorem tailTrace_3145499 : CollatzResearch.WordTrace tailWord_3145499 prefixEnd_3145499 1615152885236893954396619 := by
  unfold tailWord_3145499
  simp only [CollatzResearch.WordTrace]
  refine ⟨114725773631401806304959551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76483849087601204203306367 114725773631401806304959551)
  ·
    refine ⟨172088660447102709457439327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114725773631401806304959551 172088660447102709457439327)
    ·
      refine ⟨258132990670654064186158991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172088660447102709457439327 258132990670654064186158991)
      ·
        refine ⟨387199486005981096279238487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258132990670654064186158991 387199486005981096279238487)
        ·
          refine ⟨580799229008971644418857731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387199486005981096279238487 580799229008971644418857731)
          ·
            refine ⟨871198843513457466628286597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580799229008971644418857731 871198843513457466628286597)
            ·
              refine ⟨163349783158773274992803737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 871198843513457466628286597 163349783158773274992803737)
              ·
                refine ⟨122512337369079956244602803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163349783158773274992803737 122512337369079956244602803)
                ·
                  refine ⟨183768506053619934366904205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122512337369079956244602803 183768506053619934366904205)
                  ·
                    refine ⟨68913189770107475387589077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 183768506053619934366904205 68913189770107475387589077)
                    ·
                      refine ⟨1615152885236893954396619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68913189770107475387589077 1615152885236893954396619)
                      ·
                        rfl

theorem cell23_3145499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 7].length) (baseStart_3145499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145499 prefixEnd_3145499 := by exact prefixLift 3145499
  have htrace : WordTrace (prefixWord ++ tailWord_3145499) baseStart_3145499 baseEnd_3145499 := by
    simpa [prefixWord, tailWord_3145499, baseEnd_3145499] using wordTrace_append hprefix tailTrace_3145499
  have hstable : (prefixWord ++ tailWord_3145499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145499).length < 2 ^ (prefixWord ++ tailWord_3145499).sum := by decide
  have hdescent : baseEnd_3145499 < baseStart_3145499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145503 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 5, 1, 3]
def baseStart_3145503 : Nat := 118140960795 + 3145503 * 2 ^ 59
def prefixEnd_3145503 : Nat := 4983230072969 + 3 ^ 40 * 3145503 * 2
def baseEnd_3145503 : Nat := 1615154939159511938746601

theorem tailTrace_3145503 : CollatzResearch.WordTrace tailWord_3145503 prefixEnd_3145503 1615154939159511938746601 := by
  unfold tailWord_3145503
  simp only [CollatzResearch.WordTrace]
  refine ⟨114725919523387314988105163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76483946348924876658736775 114725919523387314988105163)
  ·
    refine ⟨172088879285080972482157745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114725919523387314988105163 172088879285080972482157745)
    ·
      refine ⟨129066659463810729361618309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172088879285080972482157745 129066659463810729361618309)
      ·
        refine ⟨24199998649464511755303433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129066659463810729361618309 24199998649464511755303433)
        ·
          refine ⟨18149998987098383816477575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24199998649464511755303433 18149998987098383816477575)
          ·
            refine ⟨27224998480647575724716363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18149998987098383816477575 27224998480647575724716363)
            ·
              refine ⟨40837497720971363587074545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27224998480647575724716363 40837497720971363587074545)
              ·
                refine ⟨30628123290728522690305909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40837497720971363587074545 30628123290728522690305909)
                ·
                  refine ⟨2871386558505799002216179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30628123290728522690305909 2871386558505799002216179)
                  ·
                    refine ⟨4307079837758698503324269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2871386558505799002216179 4307079837758698503324269)
                    ·
                      refine ⟨1615154939159511938746601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4307079837758698503324269 1615154939159511938746601)
                      ·
                        rfl

theorem cell23_3145503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_3145503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145503 prefixEnd_3145503 := by exact prefixLift 3145503
  have htrace : WordTrace (prefixWord ++ tailWord_3145503) baseStart_3145503 baseEnd_3145503 := by
    simpa [prefixWord, tailWord_3145503, baseEnd_3145503] using wordTrace_append hprefix tailTrace_3145503
  have hstable : (prefixWord ++ tailWord_3145503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145503).length < 2 ^ (prefixWord ++ tailWord_3145503).sum := by decide
  have hdescent : baseEnd_3145503 < baseStart_3145503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145543 : List Nat := [1, 1, 4, 1, 2, 1, 3, 4, 1, 1, 4]
def baseStart_3145543 : Nat := 118140960795 + 3145543 * 2 ^ 59
def prefixEnd_3145543 : Nat := 4983230072969 + 3 ^ 40 * 3145543 * 2
def baseEnd_3145543 : Nat := 1615175478385691782246417

theorem tailTrace_3145543 : CollatzResearch.WordTrace tailWord_3145543 prefixEnd_3145543 1615175478385691782246417 := by
  unfold tailWord_3145543
  simp only [CollatzResearch.WordTrace]
  refine ⟨114727378443242401819561283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76484918962161601213040855 114727378443242401819561283)
  ·
    refine ⟨172091067664863602729341925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114727378443242401819561283 172091067664863602729341925)
    ·
      refine ⟨32267075187161925511751611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172091067664863602729341925 32267075187161925511751611)
      ·
        refine ⟨48400612780742888267627417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32267075187161925511751611 48400612780742888267627417)
        ·
          refine ⟨36300459585557166200720563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48400612780742888267627417 36300459585557166200720563)
          ·
            refine ⟨54450689378335749301080845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36300459585557166200720563 54450689378335749301080845)
            ·
              refine ⟨20419008516875905987905317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54450689378335749301080845 20419008516875905987905317)
              ·
                refine ⟨3828564096914232372732247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20419008516875905987905317 3828564096914232372732247)
                ·
                  refine ⟨5742846145371348559098371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3828564096914232372732247 5742846145371348559098371)
                  ·
                    refine ⟨8614269218057022838647557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5742846145371348559098371 8614269218057022838647557)
                    ·
                      refine ⟨1615175478385691782246417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8614269218057022838647557 1615175478385691782246417)
                      ·
                        rfl

theorem cell23_3145543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_3145543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145543 prefixEnd_3145543 := by exact prefixLift 3145543
  have htrace : WordTrace (prefixWord ++ tailWord_3145543) baseStart_3145543 baseEnd_3145543 := by
    simpa [prefixWord, tailWord_3145543, baseEnd_3145543] using wordTrace_append hprefix tailTrace_3145543
  have hstable : (prefixWord ++ tailWord_3145543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145543).length < 2 ^ (prefixWord ++ tailWord_3145543).sum := by decide
  have hdescent : baseEnd_3145543 < baseStart_3145543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145546 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 3, 1, 5]
def baseStart_3145546 : Nat := 118140960795 + 3145546 * 2 ^ 59
def prefixEnd_3145546 : Nat := 4983230072969 + 3 ^ 40 * 3145546 * 2
def baseEnd_3145546 : Nat := 1615177018827655270508903

theorem tailTrace_3145546 : CollatzResearch.WordTrace tailWord_3145546 prefixEnd_3145546 1615177018827655270508903 := by
  unfold tailWord_3145546
  simp only [CollatzResearch.WordTrace]
  refine ⟨28681871965557883332980123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76484991908154355554613661 28681871965557883332980123)
  ·
    refine ⟨43022807948336824999470185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28681871965557883332980123 43022807948336824999470185)
    ·
      refine ⟨32267105961252618749602639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43022807948336824999470185 32267105961252618749602639)
      ·
        refine ⟨48400658941878928124403959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32267105961252618749602639 48400658941878928124403959)
        ·
          refine ⟨72600988412818392186605939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48400658941878928124403959 72600988412818392186605939)
          ·
            refine ⟨108901482619227588279908909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72600988412818392186605939 108901482619227588279908909)
            ·
              refine ⟨40838055982210345604965841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108901482619227588279908909 40838055982210345604965841)
              ·
                refine ⟨30628541986657759203724381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40838055982210345604965841 30628541986657759203724381)
                ·
                  refine ⟨11485703244996659701396643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30628541986657759203724381 11485703244996659701396643)
                  ·
                    refine ⟨17228554867494989552094965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11485703244996659701396643 17228554867494989552094965)
                    ·
                      refine ⟨1615177018827655270508903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17228554867494989552094965 1615177018827655270508903)
                      ·
                        rfl

theorem cell23_3145546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_3145546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145546 prefixEnd_3145546 := by exact prefixLift 3145546
  have htrace : WordTrace (prefixWord ++ tailWord_3145546) baseStart_3145546 baseEnd_3145546 := by
    simpa [prefixWord, tailWord_3145546, baseEnd_3145546] using wordTrace_append hprefix tailTrace_3145546
  have hstable : (prefixWord ++ tailWord_3145546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145546).length < 2 ^ (prefixWord ++ tailWord_3145546).sum := by decide
  have hdescent : baseEnd_3145546 < baseStart_3145546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145553 : List Nat := [1, 2, 2, 1, 5, 1, 1, 2, 4, 4]
def baseStart_3145553 : Nat := 118140960795 + 3145553 * 2 ^ 59
def prefixEnd_3145553 : Nat := 4983230072969 + 3 ^ 40 * 3145553 * 2
def baseEnd_3145553 : Nat := 538393537730745581040457

theorem tailTrace_3145553 : CollatzResearch.WordTrace tailWord_3145553 prefixEnd_3145553 538393537730745581040457 := by
  unfold tailWord_3145553
  simp only [CollatzResearch.WordTrace]
  refine ⟨114727743173206173527425313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76485162115470782351616875 114727743173206173527425313)
  ·
    refine ⟨86045807379904630145568985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114727743173206173527425313 86045807379904630145568985)
    ·
      refine ⟨64534355534928472609176739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86045807379904630145568985 64534355534928472609176739)
      ·
        refine ⟨96801533302392708913765109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64534355534928472609176739 96801533302392708913765109)
        ·
          refine ⟨9075143747099316460665479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96801533302392708913765109 9075143747099316460665479)
          ·
            refine ⟨13612715620648974690998219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9075143747099316460665479 13612715620648974690998219)
            ·
              refine ⟨20419073430973462036497329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13612715620648974690998219 20419073430973462036497329)
              ·
                refine ⟨15314305073230096527372997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20419073430973462036497329 15314305073230096527372997)
                ·
                  refine ⟨2871432201230643098882437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15314305073230096527372997 2871432201230643098882437)
                  ·
                    refine ⟨538393537730745581040457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2871432201230643098882437 538393537730745581040457)
                    ·
                      rfl

theorem cell23_3145553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 4, 4].length) (baseStart_3145553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145553 prefixEnd_3145553 := by exact prefixLift 3145553
  have htrace : WordTrace (prefixWord ++ tailWord_3145553) baseStart_3145553 baseEnd_3145553 := by
    simpa [prefixWord, tailWord_3145553, baseEnd_3145553] using wordTrace_append hprefix tailTrace_3145553
  have hstable : (prefixWord ++ tailWord_3145553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145553).length < 2 ^ (prefixWord ++ tailWord_3145553).sum := by decide
  have hdescent : baseEnd_3145553 < baseStart_3145553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145554 : List Nat := [3, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3]
def baseStart_3145554 : Nat := 118140960795 + 3145554 * 2 ^ 59
def prefixEnd_3145554 : Nat := 4983230072969 + 3 ^ 40 * 3145554 * 2
def baseEnd_3145554 : Nat := 1615181126672891239208867

theorem tailTrace_3145554 : CollatzResearch.WordTrace tailWord_3145554 prefixEnd_3145554 1615181126672891239208867 := by
  unfold tailWord_3145554
  simp only [CollatzResearch.WordTrace]
  refine ⟨28681944911550637674552929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76485186430801700465474477 28681944911550637674552929)
  ·
    refine ⟨21511458683662978255914697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28681944911550637674552929 21511458683662978255914697)
    ·
      refine ⟨16133594012747233691936023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21511458683662978255914697 16133594012747233691936023)
      ·
        refine ⟨24200391019120850537904035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16133594012747233691936023 24200391019120850537904035)
        ·
          refine ⟨36300586528681275806856053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24200391019120850537904035 36300586528681275806856053)
          ·
            refine ⟨3403179987063869606892755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36300586528681275806856053 3403179987063869606892755)
            ·
              refine ⟨5104769980595804410339133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3403179987063869606892755 5104769980595804410339133)
              ·
                refine ⟨1914288742723426653877175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5104769980595804410339133 1914288742723426653877175)
                ·
                  refine ⟨2871433114085139980815763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1914288742723426653877175 2871433114085139980815763)
                  ·
                    refine ⟨4307149671127709971223645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2871433114085139980815763 4307149671127709971223645)
                    ·
                      refine ⟨1615181126672891239208867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4307149671127709971223645 1615181126672891239208867)
                      ·
                        rfl

theorem cell23_3145554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_3145554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145554 prefixEnd_3145554 := by exact prefixLift 3145554
  have htrace : WordTrace (prefixWord ++ tailWord_3145554) baseStart_3145554 baseEnd_3145554 := by
    simpa [prefixWord, tailWord_3145554, baseEnd_3145554] using wordTrace_append hprefix tailTrace_3145554
  have hstable : (prefixWord ++ tailWord_3145554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145554).length < 2 ^ (prefixWord ++ tailWord_3145554).sum := by decide
  have hdescent : baseEnd_3145554 < baseStart_3145554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145570 : List Nat := [3, 3, 2, 1, 2, 1, 2, 1, 4, 4]
def baseStart_3145570 : Nat := 118140960795 + 3145570 * 2 ^ 59
def prefixEnd_3145570 : Nat := 4983230072969 + 3 ^ 40 * 3145570 * 2
def baseEnd_3145570 : Nat := 538396447454454392202931

theorem tailTrace_3145570 : CollatzResearch.WordTrace tailWord_3145570 prefixEnd_3145570 538396447454454392202931 := by
  unfold tailWord_3145570
  simp only [CollatzResearch.WordTrace]
  refine ⟨28682090803536146357698541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76485575476096390287196109 28682090803536146357698541)
  ·
    refine ⟨10755784051326054884136953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28682090803536146357698541 10755784051326054884136953)
    ·
      refine ⟨8066838038494541163102715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10755784051326054884136953 8066838038494541163102715)
      ·
        refine ⟨12100257057741811744654073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8066838038494541163102715 12100257057741811744654073)
        ·
          refine ⟨9075192793306358808490555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12100257057741811744654073 9075192793306358808490555)
          ·
            refine ⟨13612789189959538212735833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9075192793306358808490555 13612789189959538212735833)
            ·
              refine ⟨10209591892469653659551875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13612789189959538212735833 10209591892469653659551875)
              ·
                refine ⟨15314387838704480489327813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10209591892469653659551875 15314387838704480489327813)
                ·
                  refine ⟨2871447719757090091748965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15314387838704480489327813 2871447719757090091748965)
                  ·
                    refine ⟨538396447454454392202931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2871447719757090091748965 538396447454454392202931)
                    ·
                      rfl

theorem cell23_3145570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_3145570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145570 prefixEnd_3145570 := by exact prefixLift 3145570
  have htrace : WordTrace (prefixWord ++ tailWord_3145570) baseStart_3145570 baseEnd_3145570 := by
    simpa [prefixWord, tailWord_3145570, baseEnd_3145570] using wordTrace_append hprefix tailTrace_3145570
  have hstable : (prefixWord ++ tailWord_3145570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145570).length < 2 ^ (prefixWord ++ tailWord_3145570).sum := by decide
  have hdescent : baseEnd_3145570 < baseStart_3145570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145577 : List Nat := [1, 2, 1, 1, 1, 3, 1, 8, 1, 2, 2]
def baseStart_3145577 : Nat := 118140960795 + 3145577 * 2 ^ 59
def prefixEnd_3145577 : Nat := 4983230072969 + 3 ^ 40 * 3145577 * 2
def baseEnd_3145577 : Nat := 1615192936727944649221261

theorem tailTrace_3145577 : CollatzResearch.WordTrace tailWord_3145577 prefixEnd_3145577 1615192936727944649221261 := by
  unfold tailWord_3145577
  simp only [CollatzResearch.WordTrace]
  refine ⟨114728618525119225626298985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76485745683412817084199323 114728618525119225626298985)
  ·
    refine ⟨86046463893839419219724239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114728618525119225626298985 86046463893839419219724239)
    ·
      refine ⟨129069695840759128829586359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86046463893839419219724239 129069695840759128829586359)
      ·
        refine ⟨193604543761138693244379539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129069695840759128829586359 193604543761138693244379539)
        ·
          refine ⟨290406815641708039866569309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193604543761138693244379539 290406815641708039866569309)
          ·
            refine ⟨108902555865640514949963491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 290406815641708039866569309 108902555865640514949963491)
            ·
              refine ⟨163353833798460772424945237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108902555865640514949963491 163353833798460772424945237)
              ·
                refine ⟨1914302739825712176854827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 163353833798460772424945237 1914302739825712176854827)
                ·
                  refine ⟨2871454109738568265282241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1914302739825712176854827 2871454109738568265282241)
                  ·
                    refine ⟨2153590582303926198961681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2871454109738568265282241 2153590582303926198961681)
                    ·
                      refine ⟨1615192936727944649221261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2153590582303926198961681 1615192936727944649221261)
                      ·
                        rfl

theorem cell23_3145577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 8, 1, 2, 2].length) (baseStart_3145577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145577 prefixEnd_3145577 := by exact prefixLift 3145577
  have htrace : WordTrace (prefixWord ++ tailWord_3145577) baseStart_3145577 baseEnd_3145577 := by
    simpa [prefixWord, tailWord_3145577, baseEnd_3145577] using wordTrace_append hprefix tailTrace_3145577
  have hstable : (prefixWord ++ tailWord_3145577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145577).length < 2 ^ (prefixWord ++ tailWord_3145577).sum := by decide
  have hdescent : baseEnd_3145577 < baseStart_3145577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145586 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 1, 4, 6]
def baseStart_3145586 : Nat := 118140960795 + 3145586 * 2 ^ 59
def prefixEnd_3145586 : Nat := 4983230072969 + 3 ^ 40 * 3145586 * 2
def baseEnd_3145586 : Nat := 1615197558053835114008719

theorem tailTrace_3145586 : CollatzResearch.WordTrace tailWord_3145586 prefixEnd_3145586 1615197558053835114008719 := by
  unfold tailWord_3145586
  simp only [CollatzResearch.WordTrace]
  refine ⟨28682236695521655040844153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76485964521391080108917741 28682236695521655040844153)
  ·
    refine ⟨21511677521641241280633115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28682236695521655040844153 21511677521641241280633115)
    ·
      refine ⟨32267516282461861920949673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21511677521641241280633115 32267516282461861920949673)
      ·
        refine ⟨24200637211846396440712255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32267516282461861920949673 24200637211846396440712255)
        ·
          refine ⟨36300955817769594661068383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24200637211846396440712255 36300955817769594661068383)
          ·
            refine ⟨54451433726654391991602575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36300955817769594661068383 54451433726654391991602575)
            ·
              refine ⟨81677150589981587987403863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54451433726654391991602575 81677150589981587987403863)
              ·
                refine ⟨122515725884972381981105795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81677150589981587987403863 122515725884972381981105795)
                ·
                  refine ⟨183773588827458572971658693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122515725884972381981105795 183773588827458572971658693)
                  ·
                    refine ⟨34457547905148482432186005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 183773588827458572971658693 34457547905148482432186005)
                    ·
                      refine ⟨1615197558053835114008719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34457547905148482432186005 1615197558053835114008719)
                      ·
                        rfl

theorem cell23_3145586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_3145586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145586 prefixEnd_3145586 := by exact prefixLift 3145586
  have htrace : WordTrace (prefixWord ++ tailWord_3145586) baseStart_3145586 baseEnd_3145586 := by
    simpa [prefixWord, tailWord_3145586, baseEnd_3145586] using wordTrace_append hprefix tailTrace_3145586
  have hstable : (prefixWord ++ tailWord_3145586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145586).length < 2 ^ (prefixWord ++ tailWord_3145586).sum := by decide
  have hdescent : baseEnd_3145586 < baseStart_3145586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145593 : List Nat := [1, 2, 1, 3, 2, 2, 2, 3, 1, 3, 3]
def baseStart_3145593 : Nat := 118140960795 + 3145593 * 2 ^ 59
def prefixEnd_3145593 : Nat := 4983230072969 + 3 ^ 40 * 3145593 * 2
def baseEnd_3145593 : Nat := 1615201152418416586621187

theorem tailTrace_3145593 : CollatzResearch.WordTrace tailWord_3145593 prefixEnd_3145593 1615201152418416586621187 := by
  unfold tailWord_3145593
  simp only [CollatzResearch.WordTrace]
  refine ⟨114729202093061260358881433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76486134728707506905920955 114729202093061260358881433)
  ·
    refine ⟨86046901569795945269161075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114729202093061260358881433 86046901569795945269161075)
    ·
      refine ⟨129070352354693917903741613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86046901569795945269161075 129070352354693917903741613)
      ·
        refine ⟨48401382133010219213903105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129070352354693917903741613 48401382133010219213903105)
        ·
          refine ⟨36301036599757664410427329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48401382133010219213903105 36301036599757664410427329)
          ·
            refine ⟨27225777449818248307820497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36301036599757664410427329 27225777449818248307820497)
            ·
              refine ⟨20419333087363686230865373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27225777449818248307820497 20419333087363686230865373)
              ·
                refine ⟨7657249907761382336574515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20419333087363686230865373 7657249907761382336574515)
                ·
                  refine ⟨11485874861642073504861773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7657249907761382336574515 11485874861642073504861773)
                  ·
                    refine ⟨4307203073115777564323165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11485874861642073504861773 4307203073115777564323165)
                    ·
                      refine ⟨1615201152418416586621187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4307203073115777564323165 1615201152418416586621187)
                      ·
                        rfl

theorem cell23_3145593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_3145593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145593 prefixEnd_3145593 := by exact prefixLift 3145593
  have htrace : WordTrace (prefixWord ++ tailWord_3145593) baseStart_3145593 baseEnd_3145593 := by
    simpa [prefixWord, tailWord_3145593, baseEnd_3145593] using wordTrace_append hprefix tailTrace_3145593
  have hstable : (prefixWord ++ tailWord_3145593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145593).length < 2 ^ (prefixWord ++ tailWord_3145593).sum := by decide
  have hdescent : baseEnd_3145593 < baseStart_3145593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145614 : List Nat := [4, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5]
def baseStart_3145614 : Nat := 118140960795 + 3145614 * 2 ^ 59
def prefixEnd_3145614 : Nat := 4983230072969 + 3 ^ 40 * 3145614 * 2
def baseEnd_3145614 : Nat := 1615211935512161004458591

theorem tailTrace_3145614 : CollatzResearch.WordTrace tailWord_3145614 prefixEnd_3145614 1615211935512161004458591 := by
  unfold tailWord_3145614
  simp only [CollatzResearch.WordTrace]
  refine ⟨14341246003248147618174487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76486645350656787296930597 14341246003248147618174487)
  ·
    refine ⟨21511869004872221427261731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14341246003248147618174487 21511869004872221427261731)
    ·
      refine ⟨32267803507308332140892597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21511869004872221427261731 32267803507308332140892597)
      ·
        refine ⟨3025106578810156138208681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32267803507308332140892597 3025106578810156138208681)
        ·
          refine ⟨2268829934107617103656511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3025106578810156138208681 2268829934107617103656511)
          ·
            refine ⟨3403244901161425655484767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2268829934107617103656511 3403244901161425655484767)
            ·
              refine ⟨5104867351742138483227151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3403244901161425655484767 5104867351742138483227151)
              ·
                refine ⟨7657301027613207724840727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5104867351742138483227151 7657301027613207724840727)
                ·
                  refine ⟨11485951541419811587261091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7657301027613207724840727 11485951541419811587261091)
                  ·
                    refine ⟨17228927312129717380891637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11485951541419811587261091 17228927312129717380891637)
                    ·
                      refine ⟨1615211935512161004458591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17228927312129717380891637 1615211935512161004458591)
                      ·
                        rfl

theorem cell23_3145614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_3145614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145614 prefixEnd_3145614 := by exact prefixLift 3145614
  have htrace : WordTrace (prefixWord ++ tailWord_3145614) baseStart_3145614 baseEnd_3145614 := by
    simpa [prefixWord, tailWord_3145614, baseEnd_3145614] using wordTrace_append hprefix tailTrace_3145614
  have hstable : (prefixWord ++ tailWord_3145614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145614).length < 2 ^ (prefixWord ++ tailWord_3145614).sum := by decide
  have hdescent : baseEnd_3145614 < baseStart_3145614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145616 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 4]
def baseStart_3145616 : Nat := 118140960795 + 3145616 * 2 ^ 59
def prefixEnd_3145616 : Nat := 4983230072969 + 3 ^ 40 * 3145616 * 2
def baseEnd_3145616 : Nat := 1615212962473469996633581

theorem tailTrace_3145616 : CollatzResearch.WordTrace tailWord_3145616 prefixEnd_3145616 1615212962473469996633581 := by
  unfold tailWord_3145616
  simp only [CollatzResearch.WordTrace]
  refine ⟨57365020485988967643484351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76486693981318623524645801 57365020485988967643484351)
  ·
    refine ⟨86047530728983451465226527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57365020485988967643484351 86047530728983451465226527)
    ·
      refine ⟨129071296093475177197839791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86047530728983451465226527 129071296093475177197839791)
      ·
        refine ⟨193606944140212765796759687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129071296093475177197839791 193606944140212765796759687)
        ·
          refine ⟨290410416210319148695139531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193606944140212765796759687 290410416210319148695139531)
          ·
            refine ⟨435615624315478723042709297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290410416210319148695139531 435615624315478723042709297)
            ·
              refine ⟨326711718236609042282031973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435615624315478723042709297 326711718236609042282031973)
              ·
                refine ⟨61258447169364195427880995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 326711718236609042282031973 61258447169364195427880995)
                ·
                  refine ⟨91887670754046293141821493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61258447169364195427880995 91887670754046293141821493)
                  ·
                    refine ⟨8614469133191839982045765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91887670754046293141821493 8614469133191839982045765)
                    ·
                      refine ⟨1615212962473469996633581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8614469133191839982045765 1615212962473469996633581)
                      ·
                        rfl

theorem cell23_3145616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 4].length) (baseStart_3145616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145616 prefixEnd_3145616 := by exact prefixLift 3145616
  have htrace : WordTrace (prefixWord ++ tailWord_3145616) baseStart_3145616 baseEnd_3145616 := by
    simpa [prefixWord, tailWord_3145616, baseEnd_3145616] using wordTrace_append hprefix tailTrace_3145616
  have hstable : (prefixWord ++ tailWord_3145616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145616).length < 2 ^ (prefixWord ++ tailWord_3145616).sum := by decide
  have hdescent : baseEnd_3145616 < baseStart_3145616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145622 : List Nat := [5, 3, 1, 1, 3, 1, 2, 2, 1, 1, 3]
def baseStart_3145622 : Nat := 118140960795 + 3145622 * 2 ^ 59
def prefixEnd_3145622 : Nat := 4983230072969 + 3 ^ 40 * 3145622 * 2
def baseEnd_3145622 : Nat := 1615216043357396973158555

theorem tailTrace_3145622 : CollatzResearch.WordTrace tailWord_3145622 prefixEnd_3145622 1615216043357396973158555 := by
  unfold tailWord_3145622
  simp only [CollatzResearch.WordTrace]
  refine ⟨7170641238122262394480445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76486839873304132207791413 7170641238122262394480445)
  ·
    refine ⟨2688990464295848397930167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7170641238122262394480445 2688990464295848397930167)
    ·
      refine ⟨4033485696443772596895251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2688990464295848397930167 4033485696443772596895251)
      ·
        refine ⟨6050228544665658895342877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4033485696443772596895251 6050228544665658895342877)
        ·
          refine ⟨2268835704249622085753579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6050228544665658895342877 2268835704249622085753579)
          ·
            refine ⟨3403253556374433128630369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2268835704249622085753579 3403253556374433128630369)
            ·
              refine ⟨2552440167280824846472777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3403253556374433128630369 2552440167280824846472777)
              ·
                refine ⟨1914330125460618634854583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2552440167280824846472777 1914330125460618634854583)
                ·
                  refine ⟨2871495188190927952281875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1914330125460618634854583 2871495188190927952281875)
                  ·
                    refine ⟨4307242782286391928422813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2871495188190927952281875 4307242782286391928422813)
                    ·
                      refine ⟨1615216043357396973158555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4307242782286391928422813 1615216043357396973158555)
                      ·
                        rfl

theorem cell23_3145622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_3145622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145622 prefixEnd_3145622 := by exact prefixLift 3145622
  have htrace : WordTrace (prefixWord ++ tailWord_3145622) baseStart_3145622 baseEnd_3145622 := by
    simpa [prefixWord, tailWord_3145622, baseEnd_3145622] using wordTrace_append hprefix tailTrace_3145622
  have hstable : (prefixWord ++ tailWord_3145622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145622).length < 2 ^ (prefixWord ++ tailWord_3145622).sum := by decide
  have hdescent : baseEnd_3145622 < baseStart_3145622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145628 : List Nat := [2, 2, 3, 3, 1, 3, 2, 2, 1, 2, 2]
def baseStart_3145628 : Nat := 118140960795 + 3145628 * 2 ^ 59
def prefixEnd_3145628 : Nat := 4983230072969 + 3 ^ 40 * 3145628 * 2
def baseEnd_3145628 : Nat := 1615219124241323949683527

theorem tailTrace_3145628 : CollatzResearch.WordTrace tailWord_3145628 prefixEnd_3145628 1615219124241323949683527 := by
  unfold tailWord_3145628
  simp only [CollatzResearch.WordTrace]
  refine ⟨57365239323967230668202769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76486985765289640890937025 57365239323967230668202769)
  ·
    refine ⟨43023929492975423001152077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57365239323967230668202769 43023929492975423001152077)
    ·
      refine ⟨16133973559865783625432029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43023929492975423001152077 16133973559865783625432029)
      ·
        refine ⟨6050240084949668859537011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16133973559865783625432029 6050240084949668859537011)
        ·
          refine ⟨9075360127424503289305517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6050240084949668859537011 9075360127424503289305517)
          ·
            refine ⟨3403260047784188733489569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9075360127424503289305517 3403260047784188733489569)
            ·
              refine ⟨2552445035838141550117177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3403260047784188733489569 2552445035838141550117177)
              ·
                refine ⟨1914333776878606162587883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2552445035838141550117177 1914333776878606162587883)
                ·
                  refine ⟨2871500665317909243881825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1914333776878606162587883 2871500665317909243881825)
                  ·
                    refine ⟨2153625498988431932911369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2871500665317909243881825 2153625498988431932911369)
                    ·
                      refine ⟨1615219124241323949683527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2153625498988431932911369 1615219124241323949683527)
                      ·
                        rfl

theorem cell23_3145628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_3145628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145628 prefixEnd_3145628 := by exact prefixLift 3145628
  have htrace : WordTrace (prefixWord ++ tailWord_3145628) baseStart_3145628 baseEnd_3145628 := by
    simpa [prefixWord, tailWord_3145628, baseEnd_3145628] using wordTrace_append hprefix tailTrace_3145628
  have hstable : (prefixWord ++ tailWord_3145628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145628).length < 2 ^ (prefixWord ++ tailWord_3145628).sum := by decide
  have hdescent : baseEnd_3145628 < baseStart_3145628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145690 : List Nat := [3, 1, 1, 2, 5, 1, 2, 1, 7]
def baseStart_3145690 : Nat := 118140960795 + 3145690 * 2 ^ 59
def prefixEnd_3145690 : Nat := 4983230072969 + 3 ^ 40 * 3145690 * 2
def baseEnd_3145690 : Nat := 179472328893544745234249

theorem tailTrace_3145690 : CollatzResearch.WordTrace tailWord_3145690 prefixEnd_3145690 179472328893544745234249 := by
  unfold tailWord_3145690
  simp only [CollatzResearch.WordTrace]
  refine ⟨28683184993427461481290631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76488493315806563950108349 28683184993427461481290631)
  ·
    refine ⟨43024777490141192221935947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28683184993427461481290631 43024777490141192221935947)
    ·
      refine ⟨64537166235211788332903921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43024777490141192221935947 64537166235211788332903921)
      ·
        refine ⟨48402874676408841249677941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64537166235211788332903921 48402874676408841249677941)
        ·
          refine ⟨4537769500913328867157307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48402874676408841249677941 4537769500913328867157307)
          ·
            refine ⟨6806654251369993300735961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4537769500913328867157307 6806654251369993300735961)
            ·
              refine ⟨5104990688527494975551971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6806654251369993300735961 5104990688527494975551971)
              ·
                refine ⟨7657486032791242463327957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5104990688527494975551971 7657486032791242463327957)
                ·
                  refine ⟨179472328893544745234249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7657486032791242463327957 179472328893544745234249)
                  ·
                    rfl

theorem cell23_3145690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 7].length) (baseStart_3145690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145690 prefixEnd_3145690 := by exact prefixLift 3145690
  have htrace : WordTrace (prefixWord ++ tailWord_3145690) baseStart_3145690 baseEnd_3145690 := by
    simpa [prefixWord, tailWord_3145690, baseEnd_3145690] using wordTrace_append hprefix tailTrace_3145690
  have hstable : (prefixWord ++ tailWord_3145690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145690).length < 2 ^ (prefixWord ++ tailWord_3145690).sum := by decide
  have hdescent : baseEnd_3145690 < baseStart_3145690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145723 : List Nat := [1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 4]
def baseStart_3145723 : Nat := 118140960795 + 3145723 * 2 ^ 59
def prefixEnd_3145723 : Nat := 4983230072969 + 3 ^ 40 * 3145723 * 2
def baseEnd_3145723 : Nat := 1615267904903501077995589

theorem tailTrace_3145723 : CollatzResearch.WordTrace tailWord_3145723 prefixEnd_3145723 1615267904903501077995589 := by
  unfold tailWord_3145723
  simp only [CollatzResearch.WordTrace]
  refine ⟨114733943582590292561113823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76489295721726861707409215 114733943582590292561113823)
  ·
    refine ⟨172100915373885438841670735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114733943582590292561113823 172100915373885438841670735)
    ·
      refine ⟨258151373060828158262506103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172100915373885438841670735 258151373060828158262506103)
      ·
        refine ⟨387227059591242237393759155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258151373060828158262506103 387227059591242237393759155)
        ·
          refine ⟨580840589386863356090638733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387227059591242237393759155 580840589386863356090638733)
          ·
            refine ⟨217815221020073758533989525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 580840589386863356090638733 217815221020073758533989525)
            ·
              refine ⟨10210088485315957431280759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 217815221020073758533989525 10210088485315957431280759)
              ·
                refine ⟨15315132727973936146921139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10210088485315957431280759 15315132727973936146921139)
                ·
                  refine ⟨22972699091960904220381709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15315132727973936146921139 22972699091960904220381709)
                  ·
                    refine ⟨8614762159485339082643141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22972699091960904220381709 8614762159485339082643141)
                    ·
                      refine ⟨1615267904903501077995589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8614762159485339082643141 1615267904903501077995589)
                      ·
                        rfl

theorem cell23_3145723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 4].length) (baseStart_3145723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145723 prefixEnd_3145723 := by exact prefixLift 3145723
  have htrace : WordTrace (prefixWord ++ tailWord_3145723) baseStart_3145723 baseEnd_3145723 := by
    simpa [prefixWord, tailWord_3145723, baseEnd_3145723] using wordTrace_append hprefix tailTrace_3145723
  have hstable : (prefixWord ++ tailWord_3145723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145723).length < 2 ^ (prefixWord ++ tailWord_3145723).sum := by decide
  have hdescent : baseEnd_3145723 < baseStart_3145723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145740 : List Nat := [2, 2, 1, 2, 3, 1, 3, 2, 2, 1, 4]
def baseStart_3145740 : Nat := 118140960795 + 3145740 * 2 ^ 59
def prefixEnd_3145740 : Nat := 4983230072969 + 3 ^ 40 * 3145740 * 2
def baseEnd_3145740 : Nat := 1615276634074627511483011

theorem tailTrace_3145740 : CollatzResearch.WordTrace tailWord_3145740 prefixEnd_3145740 1615276634074627511483011 := by
  unfold tailWord_3145740
  simp only [CollatzResearch.WordTrace]
  refine ⟨57367281811764352232241337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76489709082352469642988449 57367281811764352232241337)
  ·
    refine ⟨43025461358823264174181003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57367281811764352232241337 43025461358823264174181003)
    ·
      refine ⟨64538192038234896261271505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43025461358823264174181003 64538192038234896261271505)
      ·
        refine ⟨48403644028676172195953629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64538192038234896261271505 48403644028676172195953629)
        ·
          refine ⟨18151366510753564573482611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48403644028676172195953629 18151366510753564573482611)
          ·
            refine ⟨27227049766130346860223917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18151366510753564573482611 27227049766130346860223917)
            ·
              refine ⟨10210143662298880072583969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27227049766130346860223917 10210143662298880072583969)
              ·
                refine ⟨7657607746724160054437977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10210143662298880072583969 7657607746724160054437977)
                ·
                  refine ⟨5743205810043120040828483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7657607746724160054437977 5743205810043120040828483)
                  ·
                    refine ⟨8614808715064680061242725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5743205810043120040828483 8614808715064680061242725)
                    ·
                      refine ⟨1615276634074627511483011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8614808715064680061242725 1615276634074627511483011)
                      ·
                        rfl

theorem cell23_3145740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_3145740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145740 prefixEnd_3145740 := by exact prefixLift 3145740
  have htrace : WordTrace (prefixWord ++ tailWord_3145740) baseStart_3145740 baseEnd_3145740 := by
    simpa [prefixWord, tailWord_3145740, baseEnd_3145740] using wordTrace_append hprefix tailTrace_3145740
  have hstable : (prefixWord ++ tailWord_3145740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145740).length < 2 ^ (prefixWord ++ tailWord_3145740).sum := by decide
  have hdescent : baseEnd_3145740 < baseStart_3145740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145741 : List Nat := [1, 7, 1, 2, 1, 2, 1, 1, 7]
def baseStart_3145741 : Nat := 118140960795 + 3145741 * 2 ^ 59
def prefixEnd_3145741 : Nat := 4983230072969 + 3 ^ 40 * 3145741 * 2
def baseEnd_3145741 : Nat := 179475238617253556396723

theorem tailTrace_3145741 : CollatzResearch.WordTrace tailWord_3145741 prefixEnd_3145741 179475238617253556396723 := by
  unfold tailWord_3145741
  simp only [CollatzResearch.WordTrace]
  refine ⟨114734600096525081635269077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76489733397683387756846051 114734600096525081635269077)
  ·
    refine ⟨2689092189762306600826619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 114734600096525081635269077 2689092189762306600826619)
    ·
      refine ⟨4033638284643459901239929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2689092189762306600826619 4033638284643459901239929)
      ·
        refine ⟨3025228713482594925929947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4033638284643459901239929 3025228713482594925929947)
        ·
          refine ⟨4537843070223892388894921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3025228713482594925929947 4537843070223892388894921)
          ·
            refine ⟨3403382302667919291671191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4537843070223892388894921 3403382302667919291671191)
            ·
              refine ⟨5105073454001878937506787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3403382302667919291671191 5105073454001878937506787)
              ·
                refine ⟨7657610181002818406260181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5105073454001878937506787 7657610181002818406260181)
                ·
                  refine ⟨179475238617253556396723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7657610181002818406260181 179475238617253556396723)
                  ·
                    rfl

theorem cell23_3145741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_3145741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145741 prefixEnd_3145741 := by exact prefixLift 3145741
  have htrace : WordTrace (prefixWord ++ tailWord_3145741) baseStart_3145741 baseEnd_3145741 := by
    simpa [prefixWord, tailWord_3145741, baseEnd_3145741] using wordTrace_append hprefix tailTrace_3145741
  have hstable : (prefixWord ++ tailWord_3145741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145741).length < 2 ^ (prefixWord ++ tailWord_3145741).sum := by decide
  have hdescent : baseEnd_3145741 < baseStart_3145741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145777 : List Nat := [1, 2, 2, 3, 1, 4, 2, 1, 2, 2, 3]
def baseStart_3145777 : Nat := 118140960795 + 3145777 * 2 ^ 59
def prefixEnd_3145777 : Nat := 4983230072969 + 3 ^ 40 * 3145777 * 2
def baseEnd_3145777 : Nat := 1615295632858843866720341

theorem tailTrace_3145777 : CollatzResearch.WordTrace tailWord_3145777 prefixEnd_3145777 1615295632858843866720341 := by
  unfold tailWord_3145777
  simp only [CollatzResearch.WordTrace]
  refine ⟨114735913124394659783579585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76490608749596439855719723 114735913124394659783579585)
  ·
    refine ⟨86051934843295994837684689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114735913124394659783579585 86051934843295994837684689)
    ·
      refine ⟨64538951132471996128263517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86051934843295994837684689 64538951132471996128263517)
      ·
        refine ⟨24202106674676998548098819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64538951132471996128263517 24202106674676998548098819)
        ·
          refine ⟨36303160012015497822148229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24202106674676998548098819 36303160012015497822148229)
          ·
            refine ⟨6806842502252905841652793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36303160012015497822148229 6806842502252905841652793)
            ·
              refine ⟨5105131876689679381239595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6806842502252905841652793 5105131876689679381239595)
              ·
                refine ⟨7657697815034519071859393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5105131876689679381239595 7657697815034519071859393)
                ·
                  refine ⟨5743273361275889303894545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7657697815034519071859393 5743273361275889303894545)
                  ·
                    refine ⟨4307455020956916977920909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5743273361275889303894545 4307455020956916977920909)
                    ·
                      refine ⟨1615295632858843866720341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4307455020956916977920909 1615295632858843866720341)
                      ·
                        rfl

theorem cell23_3145777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_3145777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145777 prefixEnd_3145777 := by exact prefixLift 3145777
  have htrace : WordTrace (prefixWord ++ tailWord_3145777) baseStart_3145777 baseEnd_3145777 := by
    simpa [prefixWord, tailWord_3145777, baseEnd_3145777] using wordTrace_append hprefix tailTrace_3145777
  have hstable : (prefixWord ++ tailWord_3145777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145777).length < 2 ^ (prefixWord ++ tailWord_3145777).sum := by decide
  have hdescent : baseEnd_3145777 < baseStart_3145777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145814 : List Nat := [5, 2, 2, 1, 1, 1, 2, 3, 6]
def baseStart_3145814 : Nat := 118140960795 + 3145814 * 2 ^ 59
def prefixEnd_3145814 : Nat := 4983230072969 + 3 ^ 40 * 3145814 * 2
def baseEnd_3145814 : Nat := 179479403515895580217519

theorem tailTrace_3145814 : CollatzResearch.WordTrace tailWord_3145814 prefixEnd_3145814 179479403515895580217519 := by
  unfold tailWord_3145814
  simp only [CollatzResearch.WordTrace]
  refine ⟨7171078914078788443917281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76491508416840410068450997 7171078914078788443917281)
  ·
    refine ⟨5378309185559091332937961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7171078914078788443917281 5378309185559091332937961)
    ·
      refine ⟨4033731889169318499703471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5378309185559091332937961 4033731889169318499703471)
      ·
        refine ⟨6050597833753977749555207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4033731889169318499703471 6050597833753977749555207)
        ·
          refine ⟨9075896750630966624332811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6050597833753977749555207 9075896750630966624332811)
          ·
            refine ⟨13613845125946449936499217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9075896750630966624332811 13613845125946449936499217)
            ·
              refine ⟨10210383844459837452374413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13613845125946449936499217 10210383844459837452374413)
              ·
                refine ⟨3828893941672439044640405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10210383844459837452374413 3828893941672439044640405)
                ·
                  refine ⟨179479403515895580217519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3828893941672439044640405 179479403515895580217519)
                  ·
                    rfl

theorem cell23_3145814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_3145814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145814 prefixEnd_3145814 := by exact prefixLift 3145814
  have htrace : WordTrace (prefixWord ++ tailWord_3145814) baseStart_3145814 baseEnd_3145814 := by
    simpa [prefixWord, tailWord_3145814, baseEnd_3145814] using wordTrace_append hprefix tailTrace_3145814
  have hstable : (prefixWord ++ tailWord_3145814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145814).length < 2 ^ (prefixWord ++ tailWord_3145814).sum := by decide
  have hdescent : baseEnd_3145814 < baseStart_3145814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145834 : List Nat := [3, 1, 3, 2, 3, 1, 1, 1, 1, 5, 2]
def baseStart_3145834 : Nat := 118140960795 + 3145834 * 2 ^ 59
def prefixEnd_3145834 : Nat := 4983230072969 + 3 ^ 40 * 3145834 * 2
def baseEnd_3145834 : Nat := 1615324901256150143707579

theorem tailTrace_3145834 : CollatzResearch.WordTrace tailWord_3145834 prefixEnd_3145834 1615324901256150143707579 := by
  unfold tailWord_3145834
  simp only [CollatzResearch.WordTrace]
  refine ⟨28684498021297039629601139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76491994723458772345603037 28684498021297039629601139)
  ·
    refine ⟨43026747031945559444401709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28684498021297039629601139 43026747031945559444401709)
    ·
      refine ⟨16135030136979584791650641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43026747031945559444401709 16135030136979584791650641)
      ·
        refine ⟨12101272602734688593737981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16135030136979584791650641 12101272602734688593737981)
        ·
          refine ⟨4537977226025508222651743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12101272602734688593737981 4537977226025508222651743)
          ·
            refine ⟨6806965839038262333977615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4537977226025508222651743 6806965839038262333977615)
            ·
              refine ⟨10210448758557393500966423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6806965839038262333977615 10210448758557393500966423)
              ·
                refine ⟨15315673137836090251449635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10210448758557393500966423 15315673137836090251449635)
                ·
                  refine ⟨22973509706754135377174453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15315673137836090251449635 22973509706754135377174453)
                  ·
                    refine ⟨2153766535008200191610105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22973509706754135377174453 2153766535008200191610105)
                    ·
                      refine ⟨1615324901256150143707579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2153766535008200191610105 1615324901256150143707579)
                      ·
                        rfl

theorem cell23_3145834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_3145834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145834 prefixEnd_3145834 := by exact prefixLift 3145834
  have htrace : WordTrace (prefixWord ++ tailWord_3145834) baseStart_3145834 baseEnd_3145834 := by
    simpa [prefixWord, tailWord_3145834, baseEnd_3145834] using wordTrace_append hprefix tailTrace_3145834
  have hstable : (prefixWord ++ tailWord_3145834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145834).length < 2 ^ (prefixWord ++ tailWord_3145834).sum := by decide
  have hdescent : baseEnd_3145834 < baseStart_3145834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145840 : List Nat := [2, 1, 1, 1, 5, 2, 2, 2, 1, 6]
def baseStart_3145840 : Nat := 118140960795 + 3145840 * 2 ^ 59
def prefixEnd_3145840 : Nat := 4983230072969 + 3 ^ 40 * 3145840 * 2
def baseEnd_3145840 : Nat := 538442660713359040077517

theorem tailTrace_3145840 : CollatzResearch.WordTrace tailWord_3145840 prefixEnd_3145840 538442660713359040077517 := by
  unfold tailWord_3145840
  simp only [CollatzResearch.WordTrace]
  refine ⟨57369105461583210771561487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76492140615444281028748649 57369105461583210771561487)
  ·
    refine ⟨86053658192374816157342231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57369105461583210771561487 86053658192374816157342231)
    ·
      refine ⟨129080487288562224236013347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86053658192374816157342231 129080487288562224236013347)
      ·
        refine ⟨193620730932843336354020021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129080487288562224236013347 193620730932843336354020021)
        ·
          refine ⟨18151943524954062783189377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 193620730932843336354020021 18151943524954062783189377)
          ·
            refine ⟨13613957643715547087392033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18151943524954062783189377 13613957643715547087392033)
            ·
              refine ⟨10210468232786660315544025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13613957643715547087392033 10210468232786660315544025)
              ·
                refine ⟨7657851174589995236658019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10210468232786660315544025 7657851174589995236658019)
                ·
                  refine ⟨11486776761884992854987029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7657851174589995236658019 11486776761884992854987029)
                  ·
                    refine ⟨538442660713359040077517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11486776761884992854987029 538442660713359040077517)
                    ·
                      rfl

theorem cell23_3145840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 1, 6].length) (baseStart_3145840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145840 prefixEnd_3145840 := by exact prefixLift 3145840
  have htrace : WordTrace (prefixWord ++ tailWord_3145840) baseStart_3145840 baseEnd_3145840 := by
    simpa [prefixWord, tailWord_3145840, baseEnd_3145840] using wordTrace_append hprefix tailTrace_3145840
  have hstable : (prefixWord ++ tailWord_3145840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145840).length < 2 ^ (prefixWord ++ tailWord_3145840).sum := by decide
  have hdescent : baseEnd_3145840 < baseStart_3145840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145847 : List Nat := [1, 1, 3, 1, 1, 6, 1, 3, 1, 1, 4]
def baseStart_3145847 : Nat := 118140960795 + 3145847 * 2 ^ 59
def prefixEnd_3145847 : Nat := 4983230072969 + 3 ^ 40 * 3145847 * 2
def baseEnd_3145847 : Nat := 1615331576504658592845019

theorem tailTrace_3145847 : CollatzResearch.WordTrace tailWord_3145847 prefixEnd_3145847 1615331576504658592845019 := by
  unfold tailWord_3145847
  simp only [CollatzResearch.WordTrace]
  refine ⟨114738466234141061738627795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76492310822760707825751863 114738466234141061738627795)
  ·
    refine ⟨172107699351211592607941693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114738466234141061738627795 172107699351211592607941693)
    ·
      refine ⟨64540387256704347227978135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172107699351211592607941693 64540387256704347227978135)
      ·
        refine ⟨96810580885056520841967203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64540387256704347227978135 96810580885056520841967203)
        ·
          refine ⟨145215871327584781262950805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96810580885056520841967203 145215871327584781262950805)
          ·
            refine ⟨6806993968480536621700819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 145215871327584781262950805 6806993968480536621700819)
            ·
              refine ⟨10210490952720804932551229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6806993968480536621700819 10210490952720804932551229)
              ·
                refine ⟨3828934107270301849706711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10210490952720804932551229 3828934107270301849706711)
                ·
                  refine ⟨5743401160905452774560067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3828934107270301849706711 5743401160905452774560067)
                  ·
                    refine ⟨8615101741358179161840101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5743401160905452774560067 8615101741358179161840101)
                    ·
                      refine ⟨1615331576504658592845019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8615101741358179161840101 1615331576504658592845019)
                      ·
                        rfl

theorem cell23_3145847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 1, 4].length) (baseStart_3145847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145847 prefixEnd_3145847 := by exact prefixLift 3145847
  have htrace : WordTrace (prefixWord ++ tailWord_3145847) baseStart_3145847 baseEnd_3145847 := by
    simpa [prefixWord, tailWord_3145847, baseEnd_3145847] using wordTrace_append hprefix tailTrace_3145847
  have hstable : (prefixWord ++ tailWord_3145847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145847).length < 2 ^ (prefixWord ++ tailWord_3145847).sum := by decide
  have hdescent : baseEnd_3145847 < baseStart_3145847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145860 : List Nat := [2, 3, 2, 1, 2, 1, 2, 2, 1, 1, 6]
def baseStart_3145860 : Nat := 118140960795 + 3145860 * 2 ^ 59
def prefixEnd_3145860 : Nat := 4983230072969 + 3 ^ 40 * 3145860 * 2
def baseEnd_3145860 : Nat := 1615338251753167041982459

theorem tailTrace_3145860 : CollatzResearch.WordTrace tailWord_3145860 prefixEnd_3145860 1615338251753167041982459 := by
  unfold tailWord_3145860
  simp only [CollatzResearch.WordTrace]
  refine ⟨57369470191546982479425517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76492626922062643305900689 57369470191546982479425517)
  ·
    refine ⟨21513551321830118429784569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57369470191546982479425517 21513551321830118429784569)
    ·
      refine ⟨16135163491372588822338427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21513551321830118429784569 16135163491372588822338427)
      ·
        refine ⟨24202745237058883233507641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16135163491372588822338427 24202745237058883233507641)
        ·
          refine ⟨18152058927794162425130731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24202745237058883233507641 18152058927794162425130731)
          ·
            refine ⟨27228088391691243637696097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18152058927794162425130731 27228088391691243637696097)
            ·
              refine ⟨20421066293768432728272073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27228088391691243637696097 20421066293768432728272073)
              ·
                refine ⟨15315799720326324546204055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20421066293768432728272073 15315799720326324546204055)
                ·
                  refine ⟨22973699580489486819306083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15315799720326324546204055 22973699580489486819306083)
                  ·
                    refine ⟨34460549370734230228959125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22973699580489486819306083 34460549370734230228959125)
                    ·
                      refine ⟨1615338251753167041982459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34460549370734230228959125 1615338251753167041982459)
                      ·
                        rfl

theorem cell23_3145860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_3145860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145860 prefixEnd_3145860 := by exact prefixLift 3145860
  have htrace : WordTrace (prefixWord ++ tailWord_3145860) baseStart_3145860 baseEnd_3145860 := by
    simpa [prefixWord, tailWord_3145860, baseEnd_3145860] using wordTrace_append hprefix tailTrace_3145860
  have hstable : (prefixWord ++ tailWord_3145860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145860).length < 2 ^ (prefixWord ++ tailWord_3145860).sum := by decide
  have hdescent : baseEnd_3145860 < baseStart_3145860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145884 : List Nat := [2, 2, 3, 2, 1, 1, 4, 2, 1, 2, 3]
def baseStart_3145884 : Nat := 118140960795 + 3145884 * 2 ^ 59
def prefixEnd_3145884 : Nat := 4983230072969 + 3 ^ 40 * 3145884 * 2
def baseEnd_3145884 : Nat := 1615350575288874948082349

theorem tailTrace_3145884 : CollatzResearch.WordTrace tailWord_3145884 prefixEnd_3145884 1615350575288874948082349 := by
  unfold tailWord_3145884
  simp only [CollatzResearch.WordTrace]
  refine ⟨57369907867503508528862353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76493210490004678038483137 57369907867503508528862353)
  ·
    refine ⟨43027430900627631396646765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57369907867503508528862353 43027430900627631396646765)
    ·
      refine ⟨16135286587735361773742537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43027430900627631396646765 16135286587735361773742537)
      ·
        refine ⟨12101464940801521330306903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16135286587735361773742537 12101464940801521330306903)
        ·
          refine ⟨18152197411202281995460355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12101464940801521330306903 18152197411202281995460355)
          ·
            refine ⟨27228296116803422993190533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18152197411202281995460355 27228296116803422993190533)
            ·
              refine ⟨5105305521900641811223225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27228296116803422993190533 5105305521900641811223225)
              ·
                refine ⟨3828979141425481358417419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5105305521900641811223225 3828979141425481358417419)
                ·
                  refine ⟨5743468712138222037626129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3828979141425481358417419 5743468712138222037626129)
                  ·
                    refine ⟨4307601534103666528219597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5743468712138222037626129 4307601534103666528219597)
                    ·
                      refine ⟨1615350575288874948082349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4307601534103666528219597 1615350575288874948082349)
                      ·
                        rfl

theorem cell23_3145884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_3145884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145884 prefixEnd_3145884 := by exact prefixLift 3145884
  have htrace : WordTrace (prefixWord ++ tailWord_3145884) baseStart_3145884 baseEnd_3145884 := by
    simpa [prefixWord, tailWord_3145884, baseEnd_3145884] using wordTrace_append hprefix tailTrace_3145884
  have hstable : (prefixWord ++ tailWord_3145884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145884).length < 2 ^ (prefixWord ++ tailWord_3145884).sum := by decide
  have hdescent : baseEnd_3145884 < baseStart_3145884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145887 : List Nat := [1, 1, 2, 6, 1, 1, 4, 7]
def baseStart_3145887 : Nat := 118140960795 + 3145887 * 2 ^ 59
def prefixEnd_3145887 : Nat := 4983230072969 + 3 ^ 40 * 3145887 * 2
def baseEnd_3145887 : Nat := 59827856138179201346105

theorem tailTrace_3145887 : CollatzResearch.WordTrace tailWord_3145887 prefixEnd_3145887 59827856138179201346105 := by
  unfold tailWord_3145887
  simp only [CollatzResearch.WordTrace]
  refine ⟨114739925153996148570083915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76493283435997432380055943 114739925153996148570083915)
  ·
    refine ⟨172109887730994222855125873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114739925153996148570083915 172109887730994222855125873)
    ·
      refine ⟨129082415798245667141344405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172109887730994222855125873 129082415798245667141344405)
      ·
        refine ⟨6050738240542765647250519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 129082415798245667141344405 6050738240542765647250519)
        ·
          refine ⟨9076107360814148470875779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6050738240542765647250519 9076107360814148470875779)
          ·
            refine ⟨13614161041221222706313669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9076107360814148470875779 13614161041221222706313669)
            ·
              refine ⟨2552655195228979257433813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13614161041221222706313669 2552655195228979257433813)
              ·
                refine ⟨59827856138179201346105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2552655195228979257433813 59827856138179201346105)
                ·
                  rfl

theorem cell23_3145887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 7].length) (baseStart_3145887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145887 prefixEnd_3145887 := by exact prefixLift 3145887
  have htrace : WordTrace (prefixWord ++ tailWord_3145887) baseStart_3145887 baseEnd_3145887 := by
    simpa [prefixWord, tailWord_3145887, baseEnd_3145887] using wordTrace_append hprefix tailTrace_3145887
  have hstable : (prefixWord ++ tailWord_3145887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145887).length < 2 ^ (prefixWord ++ tailWord_3145887).sum := by decide
  have hdescent : baseEnd_3145887 < baseStart_3145887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145907 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 5, 3, 2]
def baseStart_3145907 : Nat := 118140960795 + 3145907 * 2 ^ 59
def prefixEnd_3145907 : Nat := 4983230072969 + 3 ^ 40 * 3145907 * 2
def baseEnd_3145907 : Nat := 1615362385343928358094743

theorem tailTrace_3145907 : CollatzResearch.WordTrace tailWord_3145907 prefixEnd_3145907 1615362385343928358094743 := by
  unfold tailWord_3145907
  simp only [CollatzResearch.WordTrace]
  refine ⟨114740654613923691985811975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76493769742615794657207983 114740654613923691985811975)
  ·
    refine ⟨172110981920885537978717963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114740654613923691985811975 172110981920885537978717963)
    ·
      refine ⟨258166472881328306968076945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172110981920885537978717963 258166472881328306968076945)
      ·
        refine ⟨193624854660996230226057709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258166472881328306968076945 193624854660996230226057709)
        ·
          refine ⟨72609320497873586334771641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193624854660996230226057709 72609320497873586334771641)
          ·
            refine ⟨54456990373405189751078731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72609320497873586334771641 54456990373405189751078731)
            ·
              refine ⟨81685485560107784626618097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54456990373405189751078731 81685485560107784626618097)
              ·
                refine ⟨61264114170080838469963573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81685485560107784626618097 61264114170080838469963573)
                ·
                  refine ⟨5743510703445078606559085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61264114170080838469963573 5743510703445078606559085)
                  ·
                    refine ⟨2153816513791904477459657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5743510703445078606559085 2153816513791904477459657)
                    ·
                      refine ⟨1615362385343928358094743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2153816513791904477459657 1615362385343928358094743)
                      ·
                        rfl

theorem cell23_3145907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 3, 2].length) (baseStart_3145907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145907 prefixEnd_3145907 := by exact prefixLift 3145907
  have htrace : WordTrace (prefixWord ++ tailWord_3145907) baseStart_3145907 baseEnd_3145907 := by
    simpa [prefixWord, tailWord_3145907, baseEnd_3145907] using wordTrace_append hprefix tailTrace_3145907
  have hstable : (prefixWord ++ tailWord_3145907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145907).length < 2 ^ (prefixWord ++ tailWord_3145907).sum := by decide
  have hdescent : baseEnd_3145907 < baseStart_3145907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145930 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 1, 8]
def baseStart_3145930 : Nat := 118140960795 + 3145930 * 2 ^ 59
def prefixEnd_3145930 : Nat := 4983230072969 + 3 ^ 40 * 3145930 * 2
def baseEnd_3145930 : Nat := 538458065132993922702379

theorem tailTrace_3145930 : CollatzResearch.WordTrace tailWord_3145930 prefixEnd_3145930 538458065132993922702379 := by
  unfold tailWord_3145930
  simp only [CollatzResearch.WordTrace]
  refine ⟨28685373373210091728474811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76494328995226911275932829 28685373373210091728474811)
  ·
    refine ⟨43028060059815137592712217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28685373373210091728474811 43028060059815137592712217)
    ·
      refine ⟨32271045044861353194534163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43028060059815137592712217 32271045044861353194534163)
      ·
        refine ⟨48406567567292029791801245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32271045044861353194534163 48406567567292029791801245)
        ·
          refine ⟨18152462837734511171925467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48406567567292029791801245 18152462837734511171925467)
          ·
            refine ⟨27228694256601766757888201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18152462837734511171925467 27228694256601766757888201)
            ·
              refine ⟨20421520692451325068416151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27228694256601766757888201 20421520692451325068416151)
              ·
                refine ⟨30632281038676987602624227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20421520692451325068416151 30632281038676987602624227)
                ·
                  refine ⟨45948421558015481403936341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30632281038676987602624227 45948421558015481403936341)
                  ·
                    refine ⟨538458065132993922702379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45948421558015481403936341 538458065132993922702379)
                    ·
                      rfl

theorem cell23_3145930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_3145930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145930 prefixEnd_3145930 := by exact prefixLift 3145930
  have htrace : WordTrace (prefixWord ++ tailWord_3145930) baseStart_3145930 baseEnd_3145930 := by
    simpa [prefixWord, tailWord_3145930, baseEnd_3145930] using wordTrace_append hprefix tailTrace_3145930
  have hstable : (prefixWord ++ tailWord_3145930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145930).length < 2 ^ (prefixWord ++ tailWord_3145930).sum := by decide
  have hdescent : baseEnd_3145930 < baseStart_3145930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145941 : List Nat := [1, 3, 2, 4, 2, 1, 1, 1, 3, 3, 2]
def baseStart_3145941 : Nat := 118140960795 + 3145941 * 2 ^ 59
def prefixEnd_3145941 : Nat := 4983230072969 + 3 ^ 40 * 3145941 * 2
def baseEnd_3145941 : Nat := 1615379843686181225069587

theorem tailTrace_3145941 : CollatzResearch.WordTrace tailWord_3145941 prefixEnd_3145941 1615379843686181225069587 := by
  unfold tailWord_3145941
  simp only [CollatzResearch.WordTrace]
  refine ⟨114741894695800515792549677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76494596463867010528366451 114741894695800515792549677)
  ·
    refine ⟨43028210510925193422206129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114741894695800515792549677 43028210510925193422206129)
    ·
      refine ⟨32271157883193895066654597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43028210510925193422206129 32271157883193895066654597)
      ·
        refine ⟨6050842103098855324997737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32271157883193895066654597 6050842103098855324997737)
        ·
          refine ⟨4538131577324141493748303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6050842103098855324997737 4538131577324141493748303)
          ·
            refine ⟨6807197365986212240622455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4538131577324141493748303 6807197365986212240622455)
            ·
              refine ⟨10210796048979318360933683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6807197365986212240622455 10210796048979318360933683)
              ·
                refine ⟨15316194073468977541400525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10210796048979318360933683 15316194073468977541400525)
                ·
                  refine ⟨5743572777550866578025197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15316194073468977541400525 5743572777550866578025197)
                  ·
                    refine ⟨2153839791581574966759449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5743572777550866578025197 2153839791581574966759449)
                    ·
                      refine ⟨1615379843686181225069587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2153839791581574966759449 1615379843686181225069587)
                      ·
                        rfl

theorem cell23_3145941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_3145941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145941 prefixEnd_3145941 := by exact prefixLift 3145941
  have htrace : WordTrace (prefixWord ++ tailWord_3145941) baseStart_3145941 baseEnd_3145941 := by
    simpa [prefixWord, tailWord_3145941, baseEnd_3145941] using wordTrace_append hprefix tailTrace_3145941
  have hstable : (prefixWord ++ tailWord_3145941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145941).length < 2 ^ (prefixWord ++ tailWord_3145941).sum := by decide
  have hdescent : baseEnd_3145941 < baseStart_3145941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145957 : List Nat := [1, 3, 1, 4, 2, 1, 2, 1, 2, 1, 5]
def baseStart_3145957 : Nat := 118140960795 + 3145957 * 2 ^ 59
def prefixEnd_3145957 : Nat := 4983230072969 + 3 ^ 40 * 3145957 * 2
def baseEnd_3145957 : Nat := 1615388059376653162469513

theorem tailTrace_3145957 : CollatzResearch.WordTrace tailWord_3145957 prefixEnd_3145957 1615388059376653162469513 := by
  unfold tailWord_3145957
  simp only [CollatzResearch.WordTrace]
  refine ⟨114742478263742550525132125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76494985509161700350088083 114742478263742550525132125)
  ·
    refine ⟨43028429348903456446924547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114742478263742550525132125 43028429348903456446924547)
    ·
      refine ⟨64542644023355184670386821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43028429348903456446924547 64542644023355184670386821)
      ·
        refine ⟨12101745754379097125697529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64542644023355184670386821 12101745754379097125697529)
        ·
          refine ⟨9076309315784322844273147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12101745754379097125697529 9076309315784322844273147)
          ·
            refine ⟨13614463973676484266409721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9076309315784322844273147 13614463973676484266409721)
            ·
              refine ⟨10210847980257363199807291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13614463973676484266409721 10210847980257363199807291)
              ·
                refine ⟨15316271970386044799710937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10210847980257363199807291 15316271970386044799710937)
                ·
                  refine ⟨11487203977789533599783203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15316271970386044799710937 11487203977789533599783203)
                  ·
                    refine ⟨17230805966684300399674805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11487203977789533599783203 17230805966684300399674805)
                    ·
                      refine ⟨1615388059376653162469513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17230805966684300399674805 1615388059376653162469513)
                      ·
                        rfl

theorem cell23_3145957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_3145957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145957 prefixEnd_3145957 := by exact prefixLift 3145957
  have htrace : WordTrace (prefixWord ++ tailWord_3145957) baseStart_3145957 baseEnd_3145957 := by
    simpa [prefixWord, tailWord_3145957, baseEnd_3145957] using wordTrace_append hprefix tailTrace_3145957
  have hstable : (prefixWord ++ tailWord_3145957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145957).length < 2 ^ (prefixWord ++ tailWord_3145957).sum := by decide
  have hdescent : baseEnd_3145957 < baseStart_3145957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145971 : List Nat := [1, 1, 1, 2, 2, 4, 4, 2, 2, 2, 2]
def baseStart_3145971 : Nat := 118140960795 + 3145971 * 2 ^ 59
def prefixEnd_3145971 : Nat := 4983230072969 + 3 ^ 40 * 3145971 * 2
def baseEnd_3145971 : Nat := 1615395248105816107694449

theorem tailTrace_3145971 : CollatzResearch.WordTrace tailWord_3145971 prefixEnd_3145971 1615395248105816107694449 := by
  unfold tailWord_3145971
  simp only [CollatzResearch.WordTrace]
  refine ⟨114742988885691830916141767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76495325923794553944094511 114742988885691830916141767)
  ·
    refine ⟨172114483328537746374212651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114742988885691830916141767 172114483328537746374212651)
    ·
      refine ⟨258171724992806619561318977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172114483328537746374212651 258171724992806619561318977)
      ·
        refine ⟨193628793744604964670989233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258171724992806619561318977 193628793744604964670989233)
        ·
          refine ⟨145221595308453723503241925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193628793744604964670989233 145221595308453723503241925)
          ·
            refine ⟨27229049120335073156857861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145221595308453723503241925 27229049120335073156857861)
            ·
              refine ⟨5105446710062826216910849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27229049120335073156857861 5105446710062826216910849)
              ·
                refine ⟨3829085032547119662683137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5105446710062826216910849 3829085032547119662683137)
                ·
                  refine ⟨2871813774410339747012353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3829085032547119662683137 2871813774410339747012353)
                  ·
                    refine ⟨2153860330807754810259265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2871813774410339747012353 2153860330807754810259265)
                    ·
                      refine ⟨1615395248105816107694449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2153860330807754810259265 1615395248105816107694449)
                      ·
                        rfl

theorem cell23_3145971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 2, 2, 2].length) (baseStart_3145971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145971 prefixEnd_3145971 := by exact prefixLift 3145971
  have htrace : WordTrace (prefixWord ++ tailWord_3145971) baseStart_3145971 baseEnd_3145971 := by
    simpa [prefixWord, tailWord_3145971, baseEnd_3145971] using wordTrace_append hprefix tailTrace_3145971
  have hstable : (prefixWord ++ tailWord_3145971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145971).length < 2 ^ (prefixWord ++ tailWord_3145971).sum := by decide
  have hdescent : baseEnd_3145971 < baseStart_3145971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3145987 : List Nat := [1, 1, 1, 3, 2, 3, 3, 1, 2, 3, 3]
def baseStart_3145987 : Nat := 118140960795 + 3145987 * 2 ^ 59
def prefixEnd_3145987 : Nat := 4983230072969 + 3 ^ 40 * 3145987 * 2
def baseEnd_3145987 : Nat := 1615403463796288045094375

theorem tailTrace_3145987 : CollatzResearch.WordTrace tailWord_3145987 prefixEnd_3145987 1615403463796288045094375 := by
  unfold tailWord_3145987
  simp only [CollatzResearch.WordTrace]
  refine ⟨114743572453633865648724215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76495714969089243765816143 114743572453633865648724215)
  ·
    refine ⟨172115358680450798473086323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114743572453633865648724215 172115358680450798473086323)
    ·
      refine ⟨258173038020676197709629485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172115358680450798473086323 258173038020676197709629485)
      ·
        refine ⟨96814889257753574141111057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258173038020676197709629485 96814889257753574141111057)
        ·
          refine ⟨72611166943315180605833293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96814889257753574141111057 72611166943315180605833293)
          ·
            refine ⟨27229187603743192727187485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72611166943315180605833293 27229187603743192727187485)
            ·
              refine ⟨10210945351403697272695307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27229187603743192727187485 10210945351403697272695307)
              ·
                refine ⟨15316418027105545909042961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10210945351403697272695307 15316418027105545909042961)
                ·
                  refine ⟨11487313520329159431782221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15316418027105545909042961 11487313520329159431782221)
                  ·
                    refine ⟨4307742570123434786918333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11487313520329159431782221 4307742570123434786918333)
                    ·
                      refine ⟨1615403463796288045094375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4307742570123434786918333 1615403463796288045094375)
                      ·
                        rfl

theorem cell23_3145987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 3, 3].length) (baseStart_3145987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3145987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3145987 prefixEnd_3145987 := by exact prefixLift 3145987
  have htrace : WordTrace (prefixWord ++ tailWord_3145987) baseStart_3145987 baseEnd_3145987 := by
    simpa [prefixWord, tailWord_3145987, baseEnd_3145987] using wordTrace_append hprefix tailTrace_3145987
  have hstable : (prefixWord ++ tailWord_3145987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3145987).length < 2 ^ (prefixWord ++ tailWord_3145987).sum := by decide
  have hdescent : baseEnd_3145987 < baseStart_3145987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3145987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146007 : List Nat := [1, 1, 3, 4, 1, 3, 1, 1, 1, 7]
def baseStart_3146007 : Nat := 118140960795 + 3146007 * 2 ^ 59
def prefixEnd_3146007 : Nat := 4983230072969 + 3 ^ 40 * 3146007 * 2
def baseEnd_3146007 : Nat := 538471244469792655614761

theorem tailTrace_3146007 : CollatzResearch.WordTrace tailWord_3146007 prefixEnd_3146007 538471244469792655614761 := by
  unfold tailWord_3146007
  simp only [CollatzResearch.WordTrace]
  refine ⟨114744301913561409064452275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76496201275707606042968183 114744301913561409064452275)
  ·
    refine ⟨172116452870342113596678413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114744301913561409064452275 172116452870342113596678413)
    ·
      refine ⟨64543669826378292598754405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172116452870342113596678413 64543669826378292598754405)
      ·
        refine ⟨12101938092445929862266451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64543669826378292598754405 12101938092445929862266451)
        ·
          refine ⟨18152907138668894793399677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12101938092445929862266451 18152907138668894793399677)
          ·
            refine ⟨6807340177000835547524879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18152907138668894793399677 6807340177000835547524879)
            ·
              refine ⟨10211010265501253321287319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6807340177000835547524879 10211010265501253321287319)
              ·
                refine ⟨15316515398251879981930979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10211010265501253321287319 15316515398251879981930979)
                ·
                  refine ⟨22974773097377819972896469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15316515398251879981930979 22974773097377819972896469)
                  ·
                    refine ⟨538471244469792655614761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22974773097377819972896469 538471244469792655614761)
                    ·
                      rfl

theorem cell23_3146007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 7].length) (baseStart_3146007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146007 prefixEnd_3146007 := by exact prefixLift 3146007
  have htrace : WordTrace (prefixWord ++ tailWord_3146007) baseStart_3146007 baseEnd_3146007 := by
    simpa [prefixWord, tailWord_3146007, baseEnd_3146007] using wordTrace_append hprefix tailTrace_3146007
  have hstable : (prefixWord ++ tailWord_3146007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146007).length < 2 ^ (prefixWord ++ tailWord_3146007).sum := by decide
  have hdescent : baseEnd_3146007 < baseStart_3146007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146044 : List Nat := [2, 2, 2, 2, 1, 2, 1, 3, 2, 4, 2]
def baseStart_3146044 : Nat := 118140960795 + 3146044 * 2 ^ 59
def prefixEnd_3146044 : Nat := 4983230072969 + 3 ^ 40 * 3146044 * 2
def baseEnd_3146044 : Nat := 1615432732193594322081613

theorem tailTrace_3146044 : CollatzResearch.WordTrace tailWord_3146044 prefixEnd_3146044 1615432732193594322081613 := by
  unfold tailWord_3146044
  simp only [CollatzResearch.WordTrace]
  refine ⟨57372825707213682191774593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76497100942951576255699457 57372825707213682191774593)
  ·
    refine ⟨43029619280410261643830945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57372825707213682191774593 43029619280410261643830945)
    ·
      refine ⟨32272214460307696232873209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43029619280410261643830945 32272214460307696232873209)
      ·
        refine ⟨24204160845230772174654907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32272214460307696232873209 24204160845230772174654907)
        ·
          refine ⟨36306241267846158261982361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24204160845230772174654907 36306241267846158261982361)
          ·
            refine ⟨27229680950884618696486771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36306241267846158261982361 27229680950884618696486771)
            ·
              refine ⟨40844521426326928044730157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27229680950884618696486771 40844521426326928044730157)
              ·
                refine ⟨15316695534872598016773809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40844521426326928044730157 15316695534872598016773809)
                ·
                  refine ⟨11487521651154448512580357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15316695534872598016773809 11487521651154448512580357)
                  ·
                    refine ⟨2153910309591459096108817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11487521651154448512580357 2153910309591459096108817)
                    ·
                      refine ⟨1615432732193594322081613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2153910309591459096108817 1615432732193594322081613)
                      ·
                        rfl

theorem cell23_3146044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_3146044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146044 prefixEnd_3146044 := by exact prefixLift 3146044
  have htrace : WordTrace (prefixWord ++ tailWord_3146044) baseStart_3146044 baseEnd_3146044 := by
    simpa [prefixWord, tailWord_3146044, baseEnd_3146044] using wordTrace_append hprefix tailTrace_3146044
  have hstable : (prefixWord ++ tailWord_3146044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146044).length < 2 ^ (prefixWord ++ tailWord_3146044).sum := by decide
  have hdescent : baseEnd_3146044 < baseStart_3146044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146047 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 3, 4, 3]
def baseStart_3146047 : Nat := 118140960795 + 3146047 * 2 ^ 59
def prefixEnd_3146047 : Nat := 4983230072969 + 3 ^ 40 * 3146047 * 2
def baseEnd_3146047 : Nat := 1615434272635557810344099

theorem tailTrace_3146047 : CollatzResearch.WordTrace tailWord_3146047 prefixEnd_3146047 1615434272635557810344099 := by
  unfold tailWord_3146047
  simp only [CollatzResearch.WordTrace]
  refine ⟨114745760833416495895908395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76497173888944330597272263 114745760833416495895908395)
  ·
    refine ⟨172118641250124743843862593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114745760833416495895908395 172118641250124743843862593)
    ·
      refine ⟨129088980937593557882896945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172118641250124743843862593 129088980937593557882896945)
      ·
        refine ⟨96816735703195168412172709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129088980937593557882896945 96816735703195168412172709)
        ·
          refine ⟨18153137944349094077282383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96816735703195168412172709 18153137944349094077282383)
          ·
            refine ⟨27229706916523641115923575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18153137944349094077282383 27229706916523641115923575)
            ·
              refine ⟨40844560374785461673885363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27229706916523641115923575 40844560374785461673885363)
              ·
                refine ⟨61266840562178192510828045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40844560374785461673885363 61266840562178192510828045)
                ·
                  refine ⟨22975065210816822191560517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61266840562178192510828045 22975065210816822191560517)
                  ·
                    refine ⟨4307824727028154160917597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22975065210816822191560517 4307824727028154160917597)
                    ·
                      refine ⟨1615434272635557810344099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4307824727028154160917597 1615434272635557810344099)
                      ·
                        rfl

theorem cell23_3146047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 4, 3].length) (baseStart_3146047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146047 prefixEnd_3146047 := by exact prefixLift 3146047
  have htrace : WordTrace (prefixWord ++ tailWord_3146047) baseStart_3146047 baseEnd_3146047 := by
    simpa [prefixWord, tailWord_3146047, baseEnd_3146047] using wordTrace_append hprefix tailTrace_3146047
  have hstable : (prefixWord ++ tailWord_3146047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146047).length < 2 ^ (prefixWord ++ tailWord_3146047).sum := by decide
  have hdescent : baseEnd_3146047 < baseStart_3146047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146097 : List Nat := [1, 2, 2, 2, 1, 2, 1, 4, 3, 5]
def baseStart_3146097 : Nat := 118140960795 + 3146097 * 2 ^ 59
def prefixEnd_3146097 : Nat := 4983230072969 + 3 ^ 40 * 3146097 * 2
def baseEnd_3146097 : Nat := 538486648889427538239623

theorem tailTrace_3146097 : CollatzResearch.WordTrace tailWord_3146097 prefixEnd_3146097 538486648889427538239623 := by
  unfold tailWord_3146097
  simp only [CollatzResearch.WordTrace]
  refine ⟨114747584483235354435228545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76498389655490236290152363 114747584483235354435228545)
  ·
    refine ⟨86060688362426515826421409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114747584483235354435228545 86060688362426515826421409)
    ·
      refine ⟨64545516271819886869816057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86060688362426515826421409 64545516271819886869816057)
      ·
        refine ⟨48409137203864915152362043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64545516271819886869816057 48409137203864915152362043)
        ·
          refine ⟨72613705805797372728543065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48409137203864915152362043 72613705805797372728543065)
          ·
            refine ⟨54460279354348029546407299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72613705805797372728543065 54460279354348029546407299)
            ·
              refine ⟨81690419031522044319610949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54460279354348029546407299 81690419031522044319610949)
              ·
                refine ⟨15316953568410383309927053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81690419031522044319610949 15316953568410383309927053)
                ·
                  refine ⟨5743857588153893741222645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15316953568410383309927053 5743857588153893741222645)
                  ·
                    refine ⟨538486648889427538239623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5743857588153893741222645 538486648889427538239623)
                    ·
                      rfl

theorem cell23_3146097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 5].length) (baseStart_3146097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146097 prefixEnd_3146097 := by exact prefixLift 3146097
  have htrace : WordTrace (prefixWord ++ tailWord_3146097) baseStart_3146097 baseEnd_3146097 := by
    simpa [prefixWord, tailWord_3146097, baseEnd_3146097] using wordTrace_append hprefix tailTrace_3146097
  have hstable : (prefixWord ++ tailWord_3146097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146097).length < 2 ^ (prefixWord ++ tailWord_3146097).sum := by decide
  have hdescent : baseEnd_3146097 < baseStart_3146097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146101 : List Nat := [1, 3, 4, 1, 2, 1, 4, 1, 6]
def baseStart_3146101 : Nat := 118140960795 + 3146101 * 2 ^ 59
def prefixEnd_3146101 : Nat := 4983230072969 + 3 ^ 40 * 3146101 * 2
def baseEnd_3146101 : Nat := 179495777843433399896539

theorem tailTrace_3146101 : CollatzResearch.WordTrace tailWord_3146101 prefixEnd_3146101 179495777843433399896539 := by
  unfold tailWord_3146101
  simp only [CollatzResearch.WordTrace]
  refine ⟨114747730375220863118374157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76498486916813908745582771 114747730375220863118374157)
  ·
    refine ⟨43030398890707823669390309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114747730375220863118374157 43030398890707823669390309)
    ·
      refine ⟨8068199792007716938010683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43030398890707823669390309 8068199792007716938010683)
      ·
        refine ⟨12102299688011575407016025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8068199792007716938010683 12102299688011575407016025)
        ·
          refine ⟨9076724766008681555262019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12102299688011575407016025 9076724766008681555262019)
          ·
            refine ⟨13615087149013022332893029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9076724766008681555262019 13615087149013022332893029)
            ·
              refine ⟨2552828840439941687417443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13615087149013022332893029 2552828840439941687417443)
              ·
                refine ⟨3829243260659912531126165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2552828840439941687417443 3829243260659912531126165)
                ·
                  refine ⟨179495777843433399896539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3829243260659912531126165 179495777843433399896539)
                  ·
                    rfl

theorem cell23_3146101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 6].length) (baseStart_3146101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146101 prefixEnd_3146101 := by exact prefixLift 3146101
  have htrace : WordTrace (prefixWord ++ tailWord_3146101) baseStart_3146101 baseEnd_3146101 := by
    simpa [prefixWord, tailWord_3146101, baseEnd_3146101] using wordTrace_append hprefix tailTrace_3146101
  have hstable : (prefixWord ++ tailWord_3146101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146101).length < 2 ^ (prefixWord ++ tailWord_3146101).sum := by decide
  have hdescent : baseEnd_3146101 < baseStart_3146101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146121 : List Nat := [1, 2, 1, 1, 6, 1, 1, 3, 2, 3, 2]
def baseStart_3146121 : Nat := 118140960795 + 3146121 * 2 ^ 59
def prefixEnd_3146121 : Nat := 4983230072969 + 3 ^ 40 * 3146121 * 2
def baseEnd_3146121 : Nat := 1615472270203990520818759

theorem tailTrace_3146121 : CollatzResearch.WordTrace tailWord_3146121 prefixEnd_3146121 1615472270203990520818759 := by
  unfold tailWord_3146121
  simp only [CollatzResearch.WordTrace]
  refine ⟨114748459835148406534102217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76498973223432271022734811 114748459835148406534102217)
  ·
    refine ⟨86061344876361304900576663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114748459835148406534102217 86061344876361304900576663)
    ·
      refine ⟨129092017314541957350864995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86061344876361304900576663 129092017314541957350864995)
      ·
        refine ⟨193638025971812936026297493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129092017314541957350864995 193638025971812936026297493)
        ·
          refine ⟨9076782467428731376232695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 193638025971812936026297493 9076782467428731376232695)
          ·
            refine ⟨13615173701143097064349043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9076782467428731376232695 13615173701143097064349043)
            ·
              refine ⟨20422760551714645596523565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13615173701143097064349043 20422760551714645596523565)
              ·
                refine ⟨7658535206892992098696337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20422760551714645596523565 7658535206892992098696337)
                ·
                  refine ⟨5743901405169744074022253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7658535206892992098696337 5743901405169744074022253)
                  ·
                    refine ⟨2153963026938654027758345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5743901405169744074022253 2153963026938654027758345)
                    ·
                      refine ⟨1615472270203990520818759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2153963026938654027758345 1615472270203990520818759)
                      ·
                        rfl

theorem cell23_3146121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 3, 2].length) (baseStart_3146121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146121 prefixEnd_3146121 := by exact prefixLift 3146121
  have htrace : WordTrace (prefixWord ++ tailWord_3146121) baseStart_3146121 baseEnd_3146121 := by
    simpa [prefixWord, tailWord_3146121, baseEnd_3146121] using wordTrace_append hprefix tailTrace_3146121
  have hstable : (prefixWord ++ tailWord_3146121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146121).length < 2 ^ (prefixWord ++ tailWord_3146121).sum := by decide
  have hdescent : baseEnd_3146121 < baseStart_3146121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146161 : List Nat := [1, 2, 2, 4, 1, 2, 2, 3, 2, 4]
def baseStart_3146161 : Nat := 118140960795 + 3146161 * 2 ^ 59
def prefixEnd_3146161 : Nat := 4983230072969 + 3 ^ 40 * 3146161 * 2
def baseEnd_3146161 : Nat := 538497603143390121439525

theorem tailTrace_3146161 : CollatzResearch.WordTrace tailWord_3146161 prefixEnd_3146161 538497603143390121439525 := by
  unfold tailWord_3146161
  simp only [CollatzResearch.WordTrace]
  refine ⟨114749918755003493365558337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76499945836668995577038891 114749918755003493365558337)
  ·
    refine ⟨86062439066252620024168753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114749918755003493365558337 86062439066252620024168753)
    ·
      refine ⟨64546829299689465018126565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86062439066252620024168753 64546829299689465018126565)
      ·
        refine ⟨12102530493691774690898731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64546829299689465018126565 12102530493691774690898731)
        ·
          refine ⟨18153795740537662036348097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12102530493691774690898731 18153795740537662036348097)
          ·
            refine ⟨13615346805403246527261073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18153795740537662036348097 13615346805403246527261073)
            ·
              refine ⟨10211510104052434895445805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13615346805403246527261073 10211510104052434895445805)
              ·
                refine ⟨3829316289019663085792177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10211510104052434895445805 3829316289019663085792177)
                ·
                  refine ⟨2871987216764747314344133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3829316289019663085792177 2871987216764747314344133)
                  ·
                    refine ⟨538497603143390121439525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2871987216764747314344133 538497603143390121439525)
                    ·
                      rfl

theorem cell23_3146161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 2, 4].length) (baseStart_3146161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146161 prefixEnd_3146161 := by exact prefixLift 3146161
  have htrace : WordTrace (prefixWord ++ tailWord_3146161) baseStart_3146161 baseEnd_3146161 := by
    simpa [prefixWord, tailWord_3146161, baseEnd_3146161] using wordTrace_append hprefix tailTrace_3146161
  have hstable : (prefixWord ++ tailWord_3146161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146161).length < 2 ^ (prefixWord ++ tailWord_3146161).sum := by decide
  have hdescent : baseEnd_3146161 < baseStart_3146161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146188 : List Nat := [2, 2, 1, 4, 3, 1, 1, 3, 1, 2, 3]
def baseStart_3146188 : Nat := 118140960795 + 3146188 * 2 ^ 59
def prefixEnd_3146188 : Nat := 4983230072969 + 3 ^ 40 * 3146188 * 2
def baseEnd_3146188 : Nat := 1615506673407841758680951

theorem tailTrace_3146188 : CollatzResearch.WordTrace tailWord_3146188 prefixEnd_3146188 1615506673407841758680951 := by
  unfold tailWord_3146188
  simp only [CollatzResearch.WordTrace]
  refine ⟨57375451762952838488395609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76500602350603784651194145 57375451762952838488395609)
  ·
    refine ⟨43031588822214628866296707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57375451762952838488395609 43031588822214628866296707)
    ·
      refine ⟨64547383233321943299445061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43031588822214628866296707 64547383233321943299445061)
      ·
        refine ⟨12102634356247864368645949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64547383233321943299445061 12102634356247864368645949)
        ·
          refine ⟨4538487883592949138242231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12102634356247864368645949 4538487883592949138242231)
          ·
            refine ⟨6807731825389423707363347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4538487883592949138242231 6807731825389423707363347)
            ·
              refine ⟨10211597738084135561045021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6807731825389423707363347 10211597738084135561045021)
              ·
                refine ⟨3829349151781550835391883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10211597738084135561045021 3829349151781550835391883)
                ·
                  refine ⟨5744023727672326253087825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3829349151781550835391883 5744023727672326253087825)
                  ·
                    refine ⟨4308017795754244689815869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5744023727672326253087825 4308017795754244689815869)
                    ·
                      refine ⟨1615506673407841758680951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4308017795754244689815869 1615506673407841758680951)
                      ·
                        rfl

theorem cell23_3146188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_3146188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146188 prefixEnd_3146188 := by exact prefixLift 3146188
  have htrace : WordTrace (prefixWord ++ tailWord_3146188) baseStart_3146188 baseEnd_3146188 := by
    simpa [prefixWord, tailWord_3146188, baseEnd_3146188] using wordTrace_append hprefix tailTrace_3146188
  have hstable : (prefixWord ++ tailWord_3146188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146188).length < 2 ^ (prefixWord ++ tailWord_3146188).sum := by decide
  have hdescent : baseEnd_3146188 < baseStart_3146188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146201 : List Nat := [1, 2, 1, 2, 4, 1, 3, 1, 4, 1, 3]
def baseStart_3146201 : Nat := 118140960795 + 3146201 * 2 ^ 59
def prefixEnd_3146201 : Nat := 4983230072969 + 3 ^ 40 * 3146201 * 2
def baseEnd_3146201 : Nat := 1615513348656350207818391

theorem tailTrace_3146201 : CollatzResearch.WordTrace tailWord_3146201 prefixEnd_3146201 1615513348656350207818391 := by
  unfold tailWord_3146201
  simp only [CollatzResearch.WordTrace]
  refine ⟨114751377674858580197014457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76500918449905720131342971 114751377674858580197014457)
  ·
    refine ⟨86063533256143935147760843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114751377674858580197014457 86063533256143935147760843)
    ·
      refine ⟨129095299884215902721641265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86063533256143935147760843 129095299884215902721641265)
      ·
        refine ⟨96821474913161927041230949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129095299884215902721641265 96821474913161927041230949)
        ·
          refine ⟨18154026546217861320230803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96821474913161927041230949 18154026546217861320230803)
          ·
            refine ⟨27231039819326791980346205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18154026546217861320230803 27231039819326791980346205)
            ·
              refine ⟨10211639932247546992629827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27231039819326791980346205 10211639932247546992629827)
              ·
                refine ⟨15317459898371320488944741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10211639932247546992629827 15317459898371320488944741)
                ·
                  refine ⟨2872023730944622591677139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15317459898371320488944741 2872023730944622591677139)
                  ·
                    refine ⟨4308035596416933887515709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2872023730944622591677139 4308035596416933887515709)
                    ·
                      refine ⟨1615513348656350207818391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4308035596416933887515709 1615513348656350207818391)
                      ·
                        rfl

theorem cell23_3146201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 4, 1, 3].length) (baseStart_3146201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146201 prefixEnd_3146201 := by exact prefixLift 3146201
  have htrace : WordTrace (prefixWord ++ tailWord_3146201) baseStart_3146201 baseEnd_3146201 := by
    simpa [prefixWord, tailWord_3146201, baseEnd_3146201] using wordTrace_append hprefix tailTrace_3146201
  have hstable : (prefixWord ++ tailWord_3146201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146201).length < 2 ^ (prefixWord ++ tailWord_3146201).sum := by decide
  have hdescent : baseEnd_3146201 < baseStart_3146201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146217 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 1, 8]
def baseStart_3146217 : Nat := 118140960795 + 3146217 * 2 ^ 59
def prefixEnd_3146217 : Nat := 4983230072969 + 3 ^ 40 * 3146217 * 2
def baseEnd_3146217 : Nat := 538507188115607381739439

theorem tailTrace_3146217 : CollatzResearch.WordTrace tailWord_3146217 prefixEnd_3146217 538507188115607381739439 := by
  unfold tailWord_3146217
  simp only [CollatzResearch.WordTrace]
  refine ⟨114751961242800614929596905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76501307495200409953064603 114751961242800614929596905)
  ·
    refine ⟨86063970932100461197197679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114751961242800614929596905 86063970932100461197197679)
    ·
      refine ⟨129095956398150691795796519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86063970932100461197197679 129095956398150691795796519)
      ·
        refine ⟨193643934597226037693694779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129095956398150691795796519 193643934597226037693694779)
        ·
          refine ⟨290465901895839056540542169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193643934597226037693694779 290465901895839056540542169)
          ·
            refine ⟨217849426421879292405406627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290465901895839056540542169 217849426421879292405406627)
            ·
              refine ⟨326774139632818938608109941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217849426421879292405406627 326774139632818938608109941)
              ·
                refine ⟨30635075590576775494510307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 326774139632818938608109941 30635075590576775494510307)
                ·
                  refine ⟨45952613385865163241765461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30635075590576775494510307 45952613385865163241765461)
                  ·
                    refine ⟨538507188115607381739439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45952613385865163241765461 538507188115607381739439)
                    ·
                      rfl

theorem cell23_3146217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 8].length) (baseStart_3146217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146217 prefixEnd_3146217 := by exact prefixLift 3146217
  have htrace : WordTrace (prefixWord ++ tailWord_3146217) baseStart_3146217 baseEnd_3146217 := by
    simpa [prefixWord, tailWord_3146217, baseEnd_3146217] using wordTrace_append hprefix tailTrace_3146217
  have hstable : (prefixWord ++ tailWord_3146217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146217).length < 2 ^ (prefixWord ++ tailWord_3146217).sum := by decide
  have hdescent : baseEnd_3146217 < baseStart_3146217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146218 : List Nat := [3, 1, 3, 1, 3, 3, 1, 1, 1, 3, 3]
def baseStart_3146218 : Nat := 118140960795 + 3146218 * 2 ^ 59
def prefixEnd_3146218 : Nat := 4983230072969 + 3 ^ 40 * 3146218 * 2
def baseEnd_3146218 : Nat := 1615522077827476641305813

theorem tailTrace_3146218 : CollatzResearch.WordTrace tailWord_3146218 prefixEnd_3146218 1615522077827476641305813 := by
  unfold tailWord_3146218
  simp only [CollatzResearch.WordTrace]
  refine ⟨28687999428949248025095827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76501331810531328066922205 28687999428949248025095827)
  ·
    refine ⟨43031999143423872037643741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28687999428949248025095827 43031999143423872037643741)
    ·
      refine ⟨16136999678783952014116403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43031999143423872037643741 16136999678783952014116403)
      ·
        refine ⟨24205499518175928021174605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16136999678783952014116403 24205499518175928021174605)
        ·
          refine ⟨9077062319315973007940477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24205499518175928021174605 9077062319315973007940477)
          ·
            refine ⟨3403898369743489877977679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9077062319315973007940477 3403898369743489877977679)
            ·
              refine ⟨5105847554615234816966519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3403898369743489877977679 5105847554615234816966519)
              ·
                refine ⟨7658771331922852225449779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5105847554615234816966519 7658771331922852225449779)
                ·
                  refine ⟨11488156997884278338174669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7658771331922852225449779 11488156997884278338174669)
                  ·
                    refine ⟨4308058874206604376815501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11488156997884278338174669 4308058874206604376815501)
                    ·
                      refine ⟨1615522077827476641305813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4308058874206604376815501 1615522077827476641305813)
                      ·
                        rfl

theorem cell23_3146218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_3146218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146218 prefixEnd_3146218 := by exact prefixLift 3146218
  have htrace : WordTrace (prefixWord ++ tailWord_3146218) baseStart_3146218 baseEnd_3146218 := by
    simpa [prefixWord, tailWord_3146218, baseEnd_3146218] using wordTrace_append hprefix tailTrace_3146218
  have hstable : (prefixWord ++ tailWord_3146218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146218).length < 2 ^ (prefixWord ++ tailWord_3146218).sum := by decide
  have hdescent : baseEnd_3146218 < baseStart_3146218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146275 : List Nat := [1, 1, 1, 4, 4, 2, 1, 3, 2, 2, 2]
def baseStart_3146275 : Nat := 118140960795 + 3146275 * 2 ^ 59
def prefixEnd_3146275 : Nat := 4983230072969 + 3 ^ 40 * 3146275 * 2
def baseEnd_3146275 : Nat := 1615551346224782918293051

theorem tailTrace_3146275 : CollatzResearch.WordTrace tailWord_3146275 prefixEnd_3146275 1615551346224782918293051 := by
  unfold tailWord_3146275
  simp only [CollatzResearch.WordTrace]
  refine ⟨114754076676590490835208279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76502717784393660556805519 114754076676590490835208279)
  ·
    refine ⟨172131115014885736252812419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114754076676590490835208279 172131115014885736252812419)
    ·
      refine ⟨258196672522328604379218629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172131115014885736252812419 258196672522328604379218629)
      ·
        refine ⟨48411876097936613321103493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 258196672522328604379218629 48411876097936613321103493)
        ·
          refine ⟨9077226768363114997706905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48411876097936613321103493 9077226768363114997706905)
          ·
            refine ⟨6807920076272336248280179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9077226768363114997706905 6807920076272336248280179)
            ·
              refine ⟨10211880114408504372420269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6807920076272336248280179 10211880114408504372420269)
              ·
                refine ⟨3829455042903189139657601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10211880114408504372420269 3829455042903189139657601)
                ·
                  refine ⟨2872091282177391854743201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3829455042903189139657601 2872091282177391854743201)
                  ·
                    refine ⟨2154068461633043891057401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2872091282177391854743201 2154068461633043891057401)
                    ·
                      refine ⟨1615551346224782918293051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2154068461633043891057401 1615551346224782918293051)
                      ·
                        rfl

theorem cell23_3146275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 2, 2, 2].length) (baseStart_3146275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146275 prefixEnd_3146275 := by exact prefixLift 3146275
  have htrace : WordTrace (prefixWord ++ tailWord_3146275) baseStart_3146275 baseEnd_3146275 := by
    simpa [prefixWord, tailWord_3146275, baseEnd_3146275] using wordTrace_append hprefix tailTrace_3146275
  have hstable : (prefixWord ++ tailWord_3146275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146275).length < 2 ^ (prefixWord ++ tailWord_3146275).sum := by decide
  have hdescent : baseEnd_3146275 < baseStart_3146275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146279 : List Nat := [1, 1, 7, 2, 1, 2, 1, 2, 1, 3, 2]
def baseStart_3146279 : Nat := 118140960795 + 3146279 * 2 ^ 59
def prefixEnd_3146279 : Nat := 4983230072969 + 3 ^ 40 * 3146279 * 2
def baseEnd_3146279 : Nat := 1615553400147400902643033

theorem tailTrace_3146279 : CollatzResearch.WordTrace tailWord_3146279 prefixEnd_3146279 1615553400147400902643033 := by
  unfold tailWord_3146279
  simp only [CollatzResearch.WordTrace]
  refine ⟨114754222568575999518353891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76502815045717333012235927 114754222568575999518353891)
  ·
    refine ⟨172131333852863999277530837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114754222568575999518353891 172131333852863999277530837)
    ·
      refine ⟨4034328137176499983067129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 172131333852863999277530837 4034328137176499983067129)
      ·
        refine ⟨3025746102882374987300347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4034328137176499983067129 3025746102882374987300347)
        ·
          refine ⟨4538619154323562480950521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3025746102882374987300347 4538619154323562480950521)
          ·
            refine ⟨3403964365742671860712891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4538619154323562480950521 3403964365742671860712891)
            ·
              refine ⟨5105946548614007791069337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3403964365742671860712891 5105946548614007791069337)
              ·
                refine ⟨3829459911460505843302003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5105946548614007791069337 3829459911460505843302003)
                ·
                  refine ⟨5744189867190758764953005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3829459911460505843302003 5744189867190758764953005)
                  ·
                    refine ⟨2154071200196534536857377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5744189867190758764953005 2154071200196534536857377)
                    ·
                      refine ⟨1615553400147400902643033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2154071200196534536857377 1615553400147400902643033)
                      ·
                        rfl

theorem cell23_3146279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_3146279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146279 prefixEnd_3146279 := by exact prefixLift 3146279
  have htrace : WordTrace (prefixWord ++ tailWord_3146279) baseStart_3146279 baseEnd_3146279 := by
    simpa [prefixWord, tailWord_3146279, baseEnd_3146279] using wordTrace_append hprefix tailTrace_3146279
  have hstable : (prefixWord ++ tailWord_3146279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146279).length < 2 ^ (prefixWord ++ tailWord_3146279).sum := by decide
  have hdescent : baseEnd_3146279 < baseStart_3146279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146292 : List Nat := [2, 5, 1, 3, 1, 1, 1, 2, 1, 4, 2]
def baseStart_3146292 : Nat := 118140960795 + 3146292 * 2 ^ 59
def prefixEnd_3146292 : Nat := 4983230072969 + 3 ^ 40 * 3146292 * 2
def baseEnd_3146292 : Nat := 1615560075395909351780473

theorem tailTrace_3146292 : CollatzResearch.WordTrace tailWord_3146292 prefixEnd_3146292 1615560075395909351780473 := by
  unfold tailWord_3146292
  simp only [CollatzResearch.WordTrace]
  refine ⟨57377348358764451369288565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76503131145019268492384753 57377348358764451369288565)
  ·
    refine ⟨5379126408634167315870803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57377348358764451369288565 5379126408634167315870803)
    ·
      refine ⟨8068689612951250973806205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5379126408634167315870803 8068689612951250973806205)
      ·
        refine ⟨3025758604856719115177327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8068689612951250973806205 3025758604856719115177327)
        ·
          refine ⟨4538637907285078672765991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3025758604856719115177327 4538637907285078672765991)
          ·
            refine ⟨6807956860927618009148987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4538637907285078672765991 6807956860927618009148987)
            ·
              refine ⟨10211935291391427013723481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6807956860927618009148987 10211935291391427013723481)
              ·
                refine ⟨7658951468543570260292611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10211935291391427013723481 7658951468543570260292611)
                ·
                  refine ⟨11488427202815355390438917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7658951468543570260292611 11488427202815355390438917)
                  ·
                    refine ⟨2154080100527879135707297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11488427202815355390438917 2154080100527879135707297)
                    ·
                      refine ⟨1615560075395909351780473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2154080100527879135707297 1615560075395909351780473)
                      ·
                        rfl

theorem cell23_3146292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_3146292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146292 prefixEnd_3146292 := by exact prefixLift 3146292
  have htrace : WordTrace (prefixWord ++ tailWord_3146292) baseStart_3146292 baseEnd_3146292 := by
    simpa [prefixWord, tailWord_3146292, baseEnd_3146292] using wordTrace_append hprefix tailTrace_3146292
  have hstable : (prefixWord ++ tailWord_3146292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146292).length < 2 ^ (prefixWord ++ tailWord_3146292).sum := by decide
  have hdescent : baseEnd_3146292 < baseStart_3146292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146304 : List Nat := [2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 5]
def baseStart_3146304 : Nat := 118140960795 + 3146304 * 2 ^ 59
def prefixEnd_3146304 : Nat := 4983230072969 + 3 ^ 40 * 3146304 * 2
def baseEnd_3146304 : Nat := 1615566237163763304830417

theorem tailTrace_3146304 : CollatzResearch.WordTrace tailWord_3146304 prefixEnd_3146304 1615566237163763304830417 := by
  unfold tailWord_3146304
  simp only [CollatzResearch.WordTrace]
  refine ⟨57377567196742714394006983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76503422928990285858675977 57377567196742714394006983)
  ·
    refine ⟨86066350795114071591010475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57377567196742714394006983 86066350795114071591010475)
    ·
      refine ⟨129099526192671107386515713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86066350795114071591010475 129099526192671107386515713)
      ·
        refine ⟨96824644644503330539886785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129099526192671107386515713 96824644644503330539886785)
        ·
          refine ⟨72618483483377497904915089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96824644644503330539886785 72618483483377497904915089)
          ·
            refine ⟨54463862612533123428686317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72618483483377497904915089 54463862612533123428686317)
            ·
              refine ⟨20423948479699921285757369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54463862612533123428686317 20423948479699921285757369)
              ·
                refine ⟨15317961359774940964318027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20423948479699921285757369 15317961359774940964318027)
                ·
                  refine ⟨22976942039662411446477041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15317961359774940964318027 22976942039662411446477041)
                  ·
                    refine ⟨17232706529746808584857781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22976942039662411446477041 17232706529746808584857781)
                    ·
                      refine ⟨1615566237163763304830417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17232706529746808584857781 1615566237163763304830417)
                      ·
                        rfl

theorem cell23_3146304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_3146304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146304 prefixEnd_3146304 := by exact prefixLift 3146304
  have htrace : WordTrace (prefixWord ++ tailWord_3146304) baseStart_3146304 baseEnd_3146304 := by
    simpa [prefixWord, tailWord_3146304, baseEnd_3146304] using wordTrace_append hprefix tailTrace_3146304
  have hstable : (prefixWord ++ tailWord_3146304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146304).length < 2 ^ (prefixWord ++ tailWord_3146304).sum := by decide
  have hdescent : baseEnd_3146304 < baseStart_3146304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146311 : List Nat := [1, 1, 4, 1, 4, 1, 2, 2, 2, 5]
def baseStart_3146311 : Nat := 118140960795 + 3146311 * 2 ^ 59
def prefixEnd_3146311 : Nat := 4983230072969 + 3 ^ 40 * 3146311 * 2
def baseEnd_3146311 : Nat := 538523277176114925814295

theorem tailTrace_3146311 : CollatzResearch.WordTrace tailWord_3146311 prefixEnd_3146311 538523277176114925814295 := by
  unfold tailWord_3146311
  simp only [CollatzResearch.WordTrace]
  refine ⟨114755389704460068983518787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76503593136306712655679191 114755389704460068983518787)
  ·
    refine ⟨172133084556690103475278181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114755389704460068983518787 172133084556690103475278181)
    ·
      refine ⟨32274953354379394401614659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172133084556690103475278181 32274953354379394401614659)
      ·
        refine ⟨48412430031569091602421989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32274953354379394401614659 48412430031569091602421989)
        ·
          refine ⟨9077330630919204675454123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48412430031569091602421989 9077330630919204675454123)
          ·
            refine ⟨13615995946378807013181185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9077330630919204675454123 13615995946378807013181185)
            ·
              refine ⟨10211996959784105259885889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13615995946378807013181185 10211996959784105259885889)
              ·
                refine ⟨7658997719838078944914417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10211996959784105259885889 7658997719838078944914417)
                ·
                  refine ⟨5744248289878559208685813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7658997719838078944914417 5744248289878559208685813)
                  ·
                    refine ⟨538523277176114925814295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5744248289878559208685813 538523277176114925814295)
                    ·
                      rfl

theorem cell23_3146311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_3146311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146311 prefixEnd_3146311 := by exact prefixLift 3146311
  have htrace : WordTrace (prefixWord ++ tailWord_3146311) baseStart_3146311 baseEnd_3146311 := by
    simpa [prefixWord, tailWord_3146311, baseEnd_3146311] using wordTrace_append hprefix tailTrace_3146311
  have hstable : (prefixWord ++ tailWord_3146311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146311).length < 2 ^ (prefixWord ++ tailWord_3146311).sum := by decide
  have hdescent : baseEnd_3146311 < baseStart_3146311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146371 : List Nat := [1, 1, 1, 3, 3, 1, 5, 2, 6]
def baseStart_3146371 : Nat := 118140960795 + 3146371 * 2 ^ 59
def prefixEnd_3146371 : Nat := 4983230072969 + 3 ^ 40 * 3146371 * 2
def baseEnd_3146371 : Nat := 179511182263068282521401

theorem tailTrace_3146371 : CollatzResearch.WordTrace tailWord_3146371 prefixEnd_3146371 179511182263068282521401 := by
  unfold tailWord_3146371
  simp only [CollatzResearch.WordTrace]
  refine ⟨114757578084242699230702967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76505052056161799487135311 114757578084242699230702967)
  ·
    refine ⟨172136367126364048846054451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114757578084242699230702967 172136367126364048846054451)
    ·
      refine ⟨258204550689546073269081677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172136367126364048846054451 258204550689546073269081677)
      ·
        refine ⟨96826706508579777475905629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258204550689546073269081677 96826706508579777475905629)
        ·
          refine ⟨36310014940717416553464611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96826706508579777475905629 36310014940717416553464611)
          ·
            refine ⟨54465022411076124830196917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36310014940717416553464611 54465022411076124830196917)
            ·
              refine ⟨5106095851038386702830961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54465022411076124830196917 5106095851038386702830961)
              ·
                refine ⟨3829571888278790027123221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5106095851038386702830961 3829571888278790027123221)
                ·
                  refine ⟨179511182263068282521401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3829571888278790027123221 179511182263068282521401)
                  ·
                    rfl

theorem cell23_3146371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 6].length) (baseStart_3146371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146371 prefixEnd_3146371 := by exact prefixLift 3146371
  have htrace : WordTrace (prefixWord ++ tailWord_3146371) baseStart_3146371 baseEnd_3146371 := by
    simpa [prefixWord, tailWord_3146371, baseEnd_3146371] using wordTrace_append hprefix tailTrace_3146371
  have hstable : (prefixWord ++ tailWord_3146371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146371).length < 2 ^ (prefixWord ++ tailWord_3146371).sum := by decide
  have hdescent : baseEnd_3146371 < baseStart_3146371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146398 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 2, 5, 3]
def baseStart_3146398 : Nat := 118140960795 + 3146398 * 2 ^ 59
def prefixEnd_3146398 : Nat := 4983230072969 + 3 ^ 40 * 3146398 * 2
def baseEnd_3146398 : Nat := 1615614504345285937054985

theorem tailTrace_3146398 : CollatzResearch.WordTrace tailWord_3146398 prefixEnd_3146398 1615614504345285937054985 := by
  unfold tailWord_3146398
  simp only [CollatzResearch.WordTrace]
  refine ⟨14344820356893110355241981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76505708570096588561290565 14344820356893110355241981)
  ·
    refine ⟨5379307633834916383215743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14344820356893110355241981 5379307633834916383215743)
    ·
      refine ⟨8068961450752374574823615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5379307633834916383215743 8068961450752374574823615)
      ·
        refine ⟨12103442176128561862235423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8068961450752374574823615 12103442176128561862235423)
        ·
          refine ⟨18155163264192842793353135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12103442176128561862235423 18155163264192842793353135)
          ·
            refine ⟨27232744896289264190029703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18155163264192842793353135 27232744896289264190029703)
            ·
              refine ⟨40849117344433896285044555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27232744896289264190029703 40849117344433896285044555)
              ·
                refine ⟨61273676016650844427566833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40849117344433896285044555 61273676016650844427566833)
                ·
                  refine ⟨45955257012488133320675125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61273676016650844427566833 45955257012488133320675125)
                  ·
                    refine ⟨4308305344920762498813293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45955257012488133320675125 4308305344920762498813293)
                    ·
                      refine ⟨1615614504345285937054985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4308305344920762498813293 1615614504345285937054985)
                      ·
                        rfl

theorem cell23_3146398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_3146398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146398 prefixEnd_3146398 := by exact prefixLift 3146398
  have htrace : WordTrace (prefixWord ++ tailWord_3146398) baseStart_3146398 baseEnd_3146398 := by
    simpa [prefixWord, tailWord_3146398, baseEnd_3146398] using wordTrace_append hprefix tailTrace_3146398
  have hstable : (prefixWord ++ tailWord_3146398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146398).length < 2 ^ (prefixWord ++ tailWord_3146398).sum := by decide
  have hdescent : baseEnd_3146398 < baseStart_3146398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146452 : List Nat := [2, 4, 1, 3, 2, 2, 1, 2, 1, 5]
def baseStart_3146452 : Nat := 118140960795 + 3146452 * 2 ^ 59
def prefixEnd_3146452 : Nat := 4983230072969 + 3 ^ 40 * 3146452 * 2
def baseEnd_3146452 : Nat := 538547410766876241926579

theorem tailTrace_3146452 : CollatzResearch.WordTrace tailWord_3146452 prefixEnd_3146452 538547410766876241926579 := by
  unfold tailWord_3146452
  simp only [CollatzResearch.WordTrace]
  refine ⟨57380266198474625032200805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76507021597966166709601073 57380266198474625032200805)
  ·
    refine ⟨10758799912213992193537651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57380266198474625032200805 10758799912213992193537651)
    ·
      refine ⟨16138199868320988290306477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10758799912213992193537651 16138199868320988290306477)
      ·
        refine ⟨6051824950620370608864929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16138199868320988290306477 6051824950620370608864929)
        ·
          refine ⟨4538868712965277956648697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6051824950620370608864929 4538868712965277956648697)
          ·
            refine ⟨3404151534723958467486523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4538868712965277956648697 3404151534723958467486523)
            ·
              refine ⟨5106227302085937701229785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3404151534723958467486523 5106227302085937701229785)
              ·
                refine ⟨3829670476564453275922339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5106227302085937701229785 3829670476564453275922339)
                ·
                  refine ⟨5744505714846679913883509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3829670476564453275922339 5744505714846679913883509)
                  ·
                    refine ⟨538547410766876241926579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5744505714846679913883509 538547410766876241926579)
                    ·
                      rfl

theorem cell23_3146452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_3146452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146452 prefixEnd_3146452 := by exact prefixLift 3146452
  have htrace : WordTrace (prefixWord ++ tailWord_3146452) baseStart_3146452 baseEnd_3146452 := by
    simpa [prefixWord, tailWord_3146452, baseEnd_3146452] using wordTrace_append hprefix tailTrace_3146452
  have hstable : (prefixWord ++ tailWord_3146452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146452).length < 2 ^ (prefixWord ++ tailWord_3146452).sum := by decide
  have hdescent : baseEnd_3146452 < baseStart_3146452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146455 : List Nat := [1, 1, 3, 2, 1, 6, 1, 2, 1, 1, 4]
def baseStart_3146455 : Nat := 118140960795 + 3146455 * 2 ^ 59
def prefixEnd_3146455 : Nat := 4983230072969 + 3 ^ 40 * 3146455 * 2
def baseEnd_3146455 : Nat := 1615643772742592214042223

theorem tailTrace_3146455 : CollatzResearch.WordTrace tailWord_3146455 prefixEnd_3146455 1615643772742592214042223 := by
  unfold tailWord_3146455
  simp only [CollatzResearch.WordTrace]
  refine ⟨114760641815938381576760819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76507094543958921051173879 114760641815938381576760819)
  ·
    refine ⟨172140962723907572365141229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114760641815938381576760819 172140962723907572365141229)
    ·
      refine ⟨64552861021465339636927961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172140962723907572365141229 64552861021465339636927961)
      ·
        refine ⟨48414645766099004727695971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64552861021465339636927961 48414645766099004727695971)
        ·
          refine ⟨72621968649148507091543957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48414645766099004727695971 72621968649148507091543957)
          ·
            refine ⟨3404154780428836269916123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72621968649148507091543957 3404154780428836269916123)
            ·
              refine ⟨5106232170643254404874185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3404154780428836269916123 5106232170643254404874185)
              ·
                refine ⟨3829674127982440803655639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5106232170643254404874185 3829674127982440803655639)
                ·
                  refine ⟨5744511191973661205483459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3829674127982440803655639 5744511191973661205483459)
                  ·
                    refine ⟨8616766787960491808225189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5744511191973661205483459 8616766787960491808225189)
                    ·
                      refine ⟨1615643772742592214042223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8616766787960491808225189 1615643772742592214042223)
                      ·
                        rfl

theorem cell23_3146455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_3146455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146455 prefixEnd_3146455 := by exact prefixLift 3146455
  have htrace : WordTrace (prefixWord ++ tailWord_3146455) baseStart_3146455 baseEnd_3146455 := by
    simpa [prefixWord, tailWord_3146455, baseEnd_3146455] using wordTrace_append hprefix tailTrace_3146455
  have hstable : (prefixWord ++ tailWord_3146455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146455).length < 2 ^ (prefixWord ++ tailWord_3146455).sum := by decide
  have hdescent : baseEnd_3146455 < baseStart_3146455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146458 : List Nat := [3, 1, 1, 2, 2, 2, 3, 1, 3, 2, 3]
def baseStart_3146458 : Nat := 118140960795 + 3146458 * 2 ^ 59
def prefixEnd_3146458 : Nat := 4983230072969 + 3 ^ 40 * 3146458 * 2
def baseEnd_3146458 : Nat := 1615645313184555702304709

theorem tailTrace_3146458 : CollatzResearch.WordTrace tailWord_3146458 prefixEnd_3146458 1615645313184555702304709 := by
  unfold tailWord_3146458
  simp only [CollatzResearch.WordTrace]
  refine ⟨28690187808731878272280007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76507167489951675392746685 28690187808731878272280007)
  ·
    refine ⟨43035281713097817408420011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28690187808731878272280007 43035281713097817408420011)
    ·
      refine ⟨64552922569646726112630017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43035281713097817408420011 64552922569646726112630017)
      ·
        refine ⟨48414691927235044584472513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64552922569646726112630017 48414691927235044584472513)
        ·
          refine ⟨36311018945426283438354385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48414691927235044584472513 36311018945426283438354385)
          ·
            refine ⟨27233264209069712578765789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36311018945426283438354385 27233264209069712578765789)
            ·
              refine ⟨10212474078401142217037171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27233264209069712578765789 10212474078401142217037171)
              ·
                refine ⟨15318711117601713325555757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10212474078401142217037171 15318711117601713325555757)
                ·
                  refine ⟨5744516669100642497083409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15318711117601713325555757 5744516669100642497083409)
                  ·
                    refine ⟨4308387501825481872812557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5744516669100642497083409 4308387501825481872812557)
                    ·
                      refine ⟨1615645313184555702304709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4308387501825481872812557 1615645313184555702304709)
                      ·
                        rfl

theorem cell23_3146458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_3146458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146458 prefixEnd_3146458 := by exact prefixLift 3146458
  have htrace : WordTrace (prefixWord ++ tailWord_3146458) baseStart_3146458 baseEnd_3146458 := by
    simpa [prefixWord, tailWord_3146458, baseEnd_3146458] using wordTrace_append hprefix tailTrace_3146458
  have hstable : (prefixWord ++ tailWord_3146458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146458).length < 2 ^ (prefixWord ++ tailWord_3146458).sum := by decide
  have hdescent : baseEnd_3146458 < baseStart_3146458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146468 : List Nat := [2, 3, 1, 1, 1, 5, 1, 2, 1, 2, 4]
def baseStart_3146468 : Nat := 118140960795 + 3146468 * 2 ^ 59
def prefixEnd_3146468 : Nat := 4983230072969 + 3 ^ 40 * 3146468 * 2
def baseEnd_3146468 : Nat := 1615650447991100663179663

theorem tailTrace_3146468 : CollatzResearch.WordTrace tailWord_3146468 prefixEnd_3146468 1615650447991100663179663 := by
  unfold tailWord_3146468
  simp only [CollatzResearch.WordTrace]
  refine ⟨57380557982445642398492029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76507410643260856531322705 57380557982445642398492029)
  ·
    refine ⟨21517709243417115899434511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57380557982445642398492029 21517709243417115899434511)
    ·
      refine ⟨32276563865125673849151767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21517709243417115899434511 32276563865125673849151767)
      ·
        refine ⟨48414845797688510773727651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32276563865125673849151767 48414845797688510773727651)
        ·
          refine ⟨72622268696532766160591477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48414845797688510773727651 72622268696532766160591477)
          ·
            refine ⟨6808337690299946827555451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72622268696532766160591477 6808337690299946827555451)
            ·
              refine ⟨10212506535449920241333177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6808337690299946827555451 10212506535449920241333177)
              ·
                refine ⟨7659379901587440180999883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10212506535449920241333177 7659379901587440180999883)
                ·
                  refine ⟨11489069852381160271499825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7659379901587440180999883 11489069852381160271499825)
                  ·
                    refine ⟨8616802389285870203624869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11489069852381160271499825 8616802389285870203624869)
                    ·
                      refine ⟨1615650447991100663179663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8616802389285870203624869 1615650447991100663179663)
                      ·
                        rfl

theorem cell23_3146468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_3146468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146468 prefixEnd_3146468 := by exact prefixLift 3146468
  have htrace : WordTrace (prefixWord ++ tailWord_3146468) baseStart_3146468 baseEnd_3146468 := by
    simpa [prefixWord, tailWord_3146468, baseEnd_3146468] using wordTrace_append hprefix tailTrace_3146468
  have hstable : (prefixWord ++ tailWord_3146468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146468).length < 2 ^ (prefixWord ++ tailWord_3146468).sum := by decide
  have hdescent : baseEnd_3146468 < baseStart_3146468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146472 : List Nat := [2, 1, 4, 1, 4, 1, 3, 1, 1, 1, 4]
def baseStart_3146472 : Nat := 118140960795 + 3146472 * 2 ^ 59
def prefixEnd_3146472 : Nat := 4983230072969 + 3 ^ 40 * 3146472 * 2
def baseEnd_3146472 : Nat := 1615652501913718647529645

theorem tailTrace_3146472 : CollatzResearch.WordTrace tailWord_3146472 prefixEnd_3146472 1615652501913718647529645 := by
  unfold tailWord_3146472
  simp only [CollatzResearch.WordTrace]
  refine ⟨57380630928438396740064835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76507507904584528986753113 57380630928438396740064835)
  ·
    refine ⟨86070946392657595110097253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57380630928438396740064835 86070946392657595110097253)
    ·
      refine ⟨16138302448623299083143235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86070946392657595110097253 16138302448623299083143235)
      ·
        refine ⟨24207453672934948624714853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16138302448623299083143235 24207453672934948624714853)
        ·
          refine ⟨4538897563675302867134035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24207453672934948624714853 4538897563675302867134035)
          ·
            refine ⟨6808346345512954300701053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4538897563675302867134035 6808346345512954300701053)
            ·
              refine ⟨2553129879567357862762895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6808346345512954300701053 2553129879567357862762895)
              ·
                refine ⟨3829694819351036794144343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2553129879567357862762895 3829694819351036794144343)
                ·
                  refine ⟨5744542229026555191216515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3829694819351036794144343 5744542229026555191216515)
                  ·
                    refine ⟨8616813343539832786824773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5744542229026555191216515 8616813343539832786824773)
                    ·
                      refine ⟨1615652501913718647529645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8616813343539832786824773 1615652501913718647529645)
                      ·
                        rfl

theorem cell23_3146472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_3146472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146472 prefixEnd_3146472 := by exact prefixLift 3146472
  have htrace : WordTrace (prefixWord ++ tailWord_3146472) baseStart_3146472 baseEnd_3146472 := by
    simpa [prefixWord, tailWord_3146472, baseEnd_3146472] using wordTrace_append hprefix tailTrace_3146472
  have hstable : (prefixWord ++ tailWord_3146472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146472).length < 2 ^ (prefixWord ++ tailWord_3146472).sum := by decide
  have hdescent : baseEnd_3146472 < baseStart_3146472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146505 : List Nat := [1, 2, 1, 1, 3, 2, 4, 3, 2, 1, 3]
def baseStart_3146505 : Nat := 118140960795 + 3146505 * 2 ^ 59
def prefixEnd_3146505 : Nat := 4983230072969 + 3 ^ 40 * 3146505 * 2
def baseEnd_3146505 : Nat := 1615669446775317018416993

theorem tailTrace_3146505 : CollatzResearch.WordTrace tailWord_3146505 prefixEnd_3146505 1615669446775317018416993 := by
  unfold tailWord_3146505
  simp only [CollatzResearch.WordTrace]
  refine ⟨114762465465757240116080969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76508310310504826744053979 114762465465757240116080969)
  ·
    refine ⟨86071849099317930087060727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114762465465757240116080969 86071849099317930087060727)
    ·
      refine ⟨129107773648976895130591091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86071849099317930087060727 129107773648976895130591091)
      ·
        refine ⟨193661660473465342695886637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129107773648976895130591091 193661660473465342695886637)
        ·
          refine ⟨72623122677549503510957489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193661660473465342695886637 72623122677549503510957489)
          ·
            refine ⟨54467342008162127633218117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72623122677549503510957489 54467342008162127633218117)
            ·
              refine ⟨10212626626530398931228397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54467342008162127633218117 10212626626530398931228397)
              ·
                refine ⟨3829734984948899599210649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10212626626530398931228397 3829734984948899599210649)
                ·
                  refine ⟨2872301238711674699407987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3829734984948899599210649 2872301238711674699407987)
                  ·
                    refine ⟨4308451858067512049111981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2872301238711674699407987 4308451858067512049111981)
                    ·
                      refine ⟨1615669446775317018416993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4308451858067512049111981 1615669446775317018416993)
                      ·
                        rfl

theorem cell23_3146505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 2, 1, 3].length) (baseStart_3146505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146505 prefixEnd_3146505 := by exact prefixLift 3146505
  have htrace : WordTrace (prefixWord ++ tailWord_3146505) baseStart_3146505 baseEnd_3146505 := by
    simpa [prefixWord, tailWord_3146505, baseEnd_3146505] using wordTrace_append hprefix tailTrace_3146505
  have hstable : (prefixWord ++ tailWord_3146505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146505).length < 2 ^ (prefixWord ++ tailWord_3146505).sum := by decide
  have hdescent : baseEnd_3146505 < baseStart_3146505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146511 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 4]
def baseStart_3146511 : Nat := 118140960795 + 3146511 * 2 ^ 59
def prefixEnd_3146511 : Nat := 4983230072969 + 3 ^ 40 * 3146511 * 2
def baseEnd_3146511 : Nat := 1615672527659243994941965

theorem tailTrace_3146511 : CollatzResearch.WordTrace tailWord_3146511 prefixEnd_3146511 1615672527659243994941965 := by
  unfold tailWord_3146511
  simp only [CollatzResearch.WordTrace]
  refine ⟨114762684303735503140799387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76508456202490335427199591 114762684303735503140799387)
  ·
    refine ⟨172144026455603254711199081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114762684303735503140799387 172144026455603254711199081)
    ·
      refine ⟨129108019841702441033399311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172144026455603254711199081 129108019841702441033399311)
      ·
        refine ⟨193662029762553661550098967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129108019841702441033399311 193662029762553661550098967)
        ·
          refine ⟨290493044643830492325148451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193662029762553661550098967 290493044643830492325148451)
          ·
            refine ⟨435739566965745738487722677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290493044643830492325148451 435739566965745738487722677)
            ·
              refine ⟨40850584403038662983224001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 435739566965745738487722677 40850584403038662983224001)
              ·
                refine ⟨30637938302278997237418001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40850584403038662983224001 30637938302278997237418001)
                ·
                  refine ⟨22978453726709247928063501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30637938302278997237418001 22978453726709247928063501)
                  ·
                    refine ⟨8616920147515967973023813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22978453726709247928063501 8616920147515967973023813)
                    ·
                      refine ⟨1615672527659243994941965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8616920147515967973023813 1615672527659243994941965)
                      ·
                        rfl

theorem cell23_3146511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 4].length) (baseStart_3146511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146511 prefixEnd_3146511 := by exact prefixLift 3146511
  have htrace : WordTrace (prefixWord ++ tailWord_3146511) baseStart_3146511 baseEnd_3146511 := by
    simpa [prefixWord, tailWord_3146511, baseEnd_3146511] using wordTrace_append hprefix tailTrace_3146511
  have hstable : (prefixWord ++ tailWord_3146511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146511).length < 2 ^ (prefixWord ++ tailWord_3146511).sum := by decide
  have hdescent : baseEnd_3146511 < baseStart_3146511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146515 : List Nat := [1, 1, 1, 2, 1, 3, 4, 4, 1, 3, 2]
def baseStart_3146515 : Nat := 118140960795 + 3146515 * 2 ^ 59
def prefixEnd_3146515 : Nat := 4983230072969 + 3 ^ 40 * 3146515 * 2
def baseEnd_3146515 : Nat := 1615674581581861979291947

theorem tailTrace_3146515 : CollatzResearch.WordTrace tailWord_3146515 prefixEnd_3146515 1615674581581861979291947 := by
  unfold tailWord_3146515
  simp only [CollatzResearch.WordTrace]
  refine ⟨114762830195721011823944999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76508553463814007882629999 114762830195721011823944999)
  ·
    refine ⟨172144245293581517735917499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114762830195721011823944999 172144245293581517735917499)
    ·
      refine ⟨258216367940372276603876249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172144245293581517735917499 258216367940372276603876249)
      ·
        refine ⟨193662275955279207452907187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258216367940372276603876249 193662275955279207452907187)
        ·
          refine ⟨290493413932918811179360781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193662275955279207452907187 290493413932918811179360781)
          ·
            refine ⟨108935030224844554192260293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 290493413932918811179360781 108935030224844554192260293)
            ·
              refine ⟨20425318167158353911048805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108935030224844554192260293 20425318167158353911048805)
              ·
                refine ⟨3829747156342191358321651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20425318167158353911048805 3829747156342191358321651)
                ·
                  refine ⟨5744620734513287037482477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3829747156342191358321651 5744620734513287037482477)
                  ·
                    refine ⟨2154232775442482639055929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5744620734513287037482477 2154232775442482639055929)
                    ·
                      refine ⟨1615674581581861979291947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2154232775442482639055929 1615674581581861979291947)
                      ·
                        rfl

theorem cell23_3146515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 3, 2].length) (baseStart_3146515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146515 prefixEnd_3146515 := by exact prefixLift 3146515
  have htrace : WordTrace (prefixWord ++ tailWord_3146515) baseStart_3146515 baseEnd_3146515 := by
    simpa [prefixWord, tailWord_3146515, baseEnd_3146515] using wordTrace_append hprefix tailTrace_3146515
  have hstable : (prefixWord ++ tailWord_3146515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146515).length < 2 ^ (prefixWord ++ tailWord_3146515).sum := by decide
  have hdescent : baseEnd_3146515 < baseStart_3146515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146531 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 5]
def baseStart_3146531 : Nat := 118140960795 + 3146531 * 2 ^ 59
def prefixEnd_3146531 : Nat := 4983230072969 + 3 ^ 40 * 3146531 * 2
def baseEnd_3146531 : Nat := 1615682797272333916691873

theorem tailTrace_3146531 : CollatzResearch.WordTrace tailWord_3146531 prefixEnd_3146531 1615682797272333916691873 := by
  unfold tailWord_3146531
  simp only [CollatzResearch.WordTrace]
  refine ⟨114763413763663046556527447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76508942509108697704351631 114763413763663046556527447)
  ·
    refine ⟨172145120645494569834791171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114763413763663046556527447 172145120645494569834791171)
    ·
      refine ⟨258217680968241854752186757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172145120645494569834791171 258217680968241854752186757)
      ·
        refine ⟨48415815181545347766035017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 258217680968241854752186757 48415815181545347766035017)
        ·
          refine ⟨36311861386159010824526263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48415815181545347766035017 36311861386159010824526263)
          ·
            refine ⟨54467792079238516236789395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36311861386159010824526263 54467792079238516236789395)
            ·
              refine ⟨81701688118857774355184093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54467792079238516236789395 81701688118857774355184093)
              ·
                refine ⟨30638133044571665383194035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81701688118857774355184093 30638133044571665383194035)
                ·
                  refine ⟨45957199566857498074791053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30638133044571665383194035 45957199566857498074791053)
                  ·
                    refine ⟨17233949837571561778046645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45957199566857498074791053 17233949837571561778046645)
                    ·
                      refine ⟨1615682797272333916691873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17233949837571561778046645 1615682797272333916691873)
                      ·
                        rfl

theorem cell23_3146531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_3146531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146531 prefixEnd_3146531 := by exact prefixLift 3146531
  have htrace : WordTrace (prefixWord ++ tailWord_3146531) baseStart_3146531 baseEnd_3146531 := by
    simpa [prefixWord, tailWord_3146531, baseEnd_3146531] using wordTrace_append hprefix tailTrace_3146531
  have hstable : (prefixWord ++ tailWord_3146531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146531).length < 2 ^ (prefixWord ++ tailWord_3146531).sum := by decide
  have hdescent : baseEnd_3146531 < baseStart_3146531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146585 : List Nat := [1, 2, 1, 2, 2, 4, 3, 3, 5]
def baseStart_3146585 : Nat := 118140960795 + 3146585 * 2 ^ 59
def prefixEnd_3146585 : Nat := 4983230072969 + 3 ^ 40 * 3146585 * 2
def baseEnd_3146585 : Nat := 179523391691964078379625

theorem tailTrace_3146585 : CollatzResearch.WordTrace tailWord_3146585 prefixEnd_3146585 179523391691964078379625 := by
  unfold tailWord_3146585
  simp only [CollatzResearch.WordTrace]
  refine ⟨114765383305467413778993209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76510255536978275852662139 114765383305467413778993209)
  ·
    refine ⟨86074037479100560334244907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114765383305467413778993209 86074037479100560334244907)
    ·
      refine ⟨129111056218650840501367361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86074037479100560334244907 129111056218650840501367361)
      ·
        refine ⟨96833292163988130376025521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129111056218650840501367361 96833292163988130376025521)
        ·
          refine ⟨72624969122991097782019141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96833292163988130376025521 72624969122991097782019141)
          ·
            refine ⟨13617181710560830834128589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72624969122991097782019141 13617181710560830834128589)
            ·
              refine ⟨5106443141460311562798221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13617181710560830834128589 5106443141460311562798221)
              ·
                refine ⟨1914916178047616836049333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5106443141460311562798221 1914916178047616836049333)
                ·
                  refine ⟨179523391691964078379625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1914916178047616836049333 179523391691964078379625)
                  ·
                    rfl

theorem cell23_3146585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 3, 5].length) (baseStart_3146585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146585 prefixEnd_3146585 := by exact prefixLift 3146585
  have htrace : WordTrace (prefixWord ++ tailWord_3146585) baseStart_3146585 baseEnd_3146585 := by
    simpa [prefixWord, tailWord_3146585, baseEnd_3146585] using wordTrace_append hprefix tailTrace_3146585
  have hstable : (prefixWord ++ tailWord_3146585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146585).length < 2 ^ (prefixWord ++ tailWord_3146585).sum := by decide
  have hdescent : baseEnd_3146585 < baseStart_3146585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146601 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 8]
def baseStart_3146601 : Nat := 118140960795 + 3146601 * 2 ^ 59
def prefixEnd_3146601 : Nat := 4983230072969 + 3 ^ 40 * 3146601 * 2
def baseEnd_3146601 : Nat := 1615718740918148642816551

theorem tailTrace_3146601 : CollatzResearch.WordTrace tailWord_3146601 prefixEnd_3146601 1615718740918148642816551 := by
  unfold tailWord_3146601
  simp only [CollatzResearch.WordTrace]
  refine ⟨114765966873409448511575657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76510644582272965674383771 114765966873409448511575657)
  ·
    refine ⟨86074475155057086383681743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114765966873409448511575657 86074475155057086383681743)
    ·
      refine ⟨129111712732585629575522615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86074475155057086383681743 129111712732585629575522615)
      ·
        refine ⟨193667569098878444363283923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129111712732585629575522615 193667569098878444363283923)
        ·
          refine ⟨290501353648317666544925885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193667569098878444363283923 290501353648317666544925885)
          ·
            refine ⟨108938007618119124954347207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 290501353648317666544925885 108938007618119124954347207)
            ·
              refine ⟨163407011427178687431520811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108938007618119124954347207 163407011427178687431520811)
              ·
                refine ⟨245110517140768031147281217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163407011427178687431520811 245110517140768031147281217)
                ·
                  refine ⟨183832887855576023360460913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245110517140768031147281217 183832887855576023360460913)
                  ·
                    refine ⟨137874665891682017520345685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 183832887855576023360460913 137874665891682017520345685)
                    ·
                      refine ⟨1615718740918148642816551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 137874665891682017520345685 1615718740918148642816551)
                      ·
                        rfl

theorem cell23_3146601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 8].length) (baseStart_3146601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146601 prefixEnd_3146601 := by exact prefixLift 3146601
  have htrace : WordTrace (prefixWord ++ tailWord_3146601) baseStart_3146601 baseEnd_3146601 := by
    simpa [prefixWord, tailWord_3146601, baseEnd_3146601] using wordTrace_append hprefix tailTrace_3146601
  have hstable : (prefixWord ++ tailWord_3146601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146601).length < 2 ^ (prefixWord ++ tailWord_3146601).sum := by decide
  have hdescent : baseEnd_3146601 < baseStart_3146601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146605 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 2, 5, 2]
def baseStart_3146605 : Nat := 118140960795 + 3146605 * 2 ^ 59
def prefixEnd_3146605 : Nat := 4983230072969 + 3 ^ 40 * 3146605 * 2
def baseEnd_3146605 : Nat := 1615720794840766627166533

theorem tailTrace_3146605 : CollatzResearch.WordTrace tailWord_3146605 prefixEnd_3146605 1615720794840766627166533 := by
  unfold tailWord_3146605
  simp only [CollatzResearch.WordTrace]
  refine ⟨114766112765394957194721269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76510741843596638129814179 114766112765394957194721269)
  ·
    refine ⟨10759323071755777237005119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114766112765394957194721269 10759323071755777237005119)
    ·
      refine ⟨16138984607633665855507679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10759323071755777237005119 16138984607633665855507679)
      ·
        refine ⟨24208476911450498783261519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16138984607633665855507679 24208476911450498783261519)
        ·
          refine ⟨36312715367175748174892279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24208476911450498783261519 36312715367175748174892279)
          ·
            refine ⟨54469073050763622262338419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36312715367175748174892279 54469073050763622262338419)
            ·
              refine ⟨81703609576145433393507629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54469073050763622262338419 81703609576145433393507629)
              ·
                refine ⟨30638853591054537522565361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81703609576145433393507629 30638853591054537522565361)
                ·
                  refine ⟨22979140193290903141924021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30638853591054537522565361 22979140193290903141924021)
                  ·
                    refine ⟨2154294393121022169555377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22979140193290903141924021 2154294393121022169555377)
                    ·
                      refine ⟨1615720794840766627166533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2154294393121022169555377 1615720794840766627166533)
                      ·
                        rfl

theorem cell23_3146605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_3146605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146605 prefixEnd_3146605 := by exact prefixLift 3146605
  have htrace : WordTrace (prefixWord ++ tailWord_3146605) baseStart_3146605 baseEnd_3146605 := by
    simpa [prefixWord, tailWord_3146605, baseEnd_3146605] using wordTrace_append hprefix tailTrace_3146605
  have hstable : (prefixWord ++ tailWord_3146605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146605).length < 2 ^ (prefixWord ++ tailWord_3146605).sum := by decide
  have hdescent : baseEnd_3146605 < baseStart_3146605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146618 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4]
def baseStart_3146618 : Nat := 118140960795 + 3146618 * 2 ^ 59
def prefixEnd_3146618 : Nat := 4983230072969 + 3 ^ 40 * 3146618 * 2
def baseEnd_3146618 : Nat := 1615727470089275076303973

theorem tailTrace_3146618 : CollatzResearch.WordTrace tailWord_3146618 prefixEnd_3146618 1615727470089275076303973 := by
  unfold tailWord_3146618
  simp only [CollatzResearch.WordTrace]
  refine ⟨28691646728586965103736127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76511057942898573609963005 28691646728586965103736127)
  ·
    refine ⟨43037470092880447655604191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28691646728586965103736127 43037470092880447655604191)
    ·
      refine ⟨64556205139320671483406287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43037470092880447655604191 64556205139320671483406287)
      ·
        refine ⟨96834307708981007225109431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64556205139320671483406287 96834307708981007225109431)
        ·
          refine ⟨145251461563471510837664147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96834307708981007225109431 145251461563471510837664147)
          ·
            refine ⟨217877192345207266256496221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145251461563471510837664147 217877192345207266256496221)
            ·
              refine ⟨81703947129452724846186083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217877192345207266256496221 81703947129452724846186083)
              ·
                refine ⟨122555920694179087269279125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81703947129452724846186083 122555920694179087269279125)
                ·
                  refine ⟨5744808782539644715747459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 122555920694179087269279125 5744808782539644715747459)
                  ·
                    refine ⟨8617213173809467073621189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5744808782539644715747459 8617213173809467073621189)
                    ·
                      refine ⟨1615727470089275076303973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8617213173809467073621189 1615727470089275076303973)
                      ·
                        rfl

theorem cell23_3146618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_3146618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146618 prefixEnd_3146618 := by exact prefixLift 3146618
  have htrace : WordTrace (prefixWord ++ tailWord_3146618) baseStart_3146618 baseEnd_3146618 := by
    simpa [prefixWord, tailWord_3146618, baseEnd_3146618] using wordTrace_append hprefix tailTrace_3146618
  have hstable : (prefixWord ++ tailWord_3146618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146618).length < 2 ^ (prefixWord ++ tailWord_3146618).sum := by decide
  have hdescent : baseEnd_3146618 < baseStart_3146618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146698 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 2, 4, 5]
def baseStart_3146698 : Nat := 118140960795 + 3146698 * 2 ^ 59
def prefixEnd_3146698 : Nat := 4983230072969 + 3 ^ 40 * 3146698 * 2
def baseEnd_3146698 : Nat := 1615768548541634763303605

theorem tailTrace_3146698 : CollatzResearch.WordTrace tailWord_3146698 prefixEnd_3146698 1615768548541634763303605 := by
  unfold tailWord_3146698
  simp only [CollatzResearch.WordTrace]
  refine ⟨28692376188514508519464187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76513003169372022718571165 28692376188514508519464187)
  ·
    refine ⟨43038564282771762779196281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28692376188514508519464187 43038564282771762779196281)
    ·
      refine ⟨32278923212078822084397211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43038564282771762779196281 32278923212078822084397211)
      ·
        refine ⟨48418384818118233126595817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32278923212078822084397211 48418384818118233126595817)
        ·
          refine ⟨36313788613588674844946863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48418384818118233126595817 36313788613588674844946863)
          ·
            refine ⟨54470682920383012267420295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36313788613588674844946863 54470682920383012267420295)
            ·
              refine ⟨81706024380574518401130443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54470682920383012267420295 81706024380574518401130443)
              ·
                refine ⟨122559036570861777601695665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81706024380574518401130443 122559036570861777601695665)
                ·
                  refine ⟨91919277428146333201271749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122559036570861777601695665 91919277428146333201271749)
                  ·
                    refine ⟨17234864517777437475238453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91919277428146333201271749 17234864517777437475238453)
                    ·
                      refine ⟨1615768548541634763303605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17234864517777437475238453 1615768548541634763303605)
                      ·
                        rfl

theorem cell23_3146698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_3146698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146698 prefixEnd_3146698 := by exact prefixLift 3146698
  have htrace : WordTrace (prefixWord ++ tailWord_3146698) baseStart_3146698 baseEnd_3146698 := by
    simpa [prefixWord, tailWord_3146698, baseEnd_3146698] using wordTrace_append hprefix tailTrace_3146698
  have hstable : (prefixWord ++ tailWord_3146698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146698).length < 2 ^ (prefixWord ++ tailWord_3146698).sum := by decide
  have hdescent : baseEnd_3146698 < baseStart_3146698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146705 : List Nat := [1, 2, 2, 1, 2, 1, 5, 3, 1, 5]
def baseStart_3146705 : Nat := 118140960795 + 3146705 * 2 ^ 59
def prefixEnd_3146705 : Nat := 4983230072969 + 3 ^ 40 * 3146705 * 2
def baseEnd_3146705 : Nat := 538590714302072078638691

theorem tailTrace_3146705 : CollatzResearch.WordTrace tailWord_3146705 prefixEnd_3146705 538590714302072078638691 := by
  unfold tailWord_3146705
  simp only [CollatzResearch.WordTrace]
  refine ⟨114769760065032674273361569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76513173376688449515574379 114769760065032674273361569)
  ·
    refine ⟨86077320048774505705021177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114769760065032674273361569 86077320048774505705021177)
    ·
      refine ⟨64557990036580879278765883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86077320048774505705021177 64557990036580879278765883)
      ·
        refine ⟨96836985054871318918148825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64557990036580879278765883 96836985054871318918148825)
        ·
          refine ⟨72627738791153489188611619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96836985054871318918148825 72627738791153489188611619)
          ·
            refine ⟨108941608186730233782917429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72627738791153489188611619 108941608186730233782917429)
            ·
              refine ⟨10213275767505959417148509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108941608186730233782917429 10213275767505959417148509)
              ·
                refine ⟨3829978412814734781430691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10213275767505959417148509 3829978412814734781430691)
                ·
                  refine ⟨5744967619222102172146037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3829978412814734781430691 5744967619222102172146037)
                  ·
                    refine ⟨538590714302072078638691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5744967619222102172146037 538590714302072078638691)
                    ·
                      rfl

theorem cell23_3146705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 5].length) (baseStart_3146705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146705 prefixEnd_3146705 := by exact prefixLift 3146705
  have htrace : WordTrace (prefixWord ++ tailWord_3146705) baseStart_3146705 baseEnd_3146705 := by
    simpa [prefixWord, tailWord_3146705, baseEnd_3146705] using wordTrace_append hprefix tailTrace_3146705
  have hstable : (prefixWord ++ tailWord_3146705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146705).length < 2 ^ (prefixWord ++ tailWord_3146705).sum := by decide
  have hdescent : baseEnd_3146705 < baseStart_3146705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146709 : List Nat := [1, 3, 2, 3, 4, 1, 1, 2, 6]
def baseStart_3146709 : Nat := 118140960795 + 3146709 * 2 ^ 59
def prefixEnd_3146709 : Nat := 4983230072969 + 3 ^ 40 * 3146709 * 2
def baseEnd_3146709 : Nat := 179530466314314913362895

theorem tailTrace_3146709 : CollatzResearch.WordTrace tailWord_3146709 prefixEnd_3146709 179530466314314913362895 := by
  unfold tailWord_3146709
  simp only [CollatzResearch.WordTrace]
  refine ⟨114769905957018182956507181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76513270638012121971004787 114769905957018182956507181)
  ·
    refine ⟨43038714733881818608690193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114769905957018182956507181 43038714733881818608690193)
    ·
      refine ⟨32279036050411363956517645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43038714733881818608690193 32279036050411363956517645)
      ·
        refine ⟨12104638518904261483694117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32279036050411363956517645 12104638518904261483694117)
        ·
          refine ⟨2269619722294549028192647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12104638518904261483694117 2269619722294549028192647)
          ·
            refine ⟨3404429583441823542288971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2269619722294549028192647 3404429583441823542288971)
            ·
              refine ⟨5106644375162735313433457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3404429583441823542288971 5106644375162735313433457)
              ·
                refine ⟨3829983281372051485075093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5106644375162735313433457 3829983281372051485075093)
                ·
                  refine ⟨179530466314314913362895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3829983281372051485075093 179530466314314913362895)
                  ·
                    rfl

theorem cell23_3146709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 6].length) (baseStart_3146709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146709 prefixEnd_3146709 := by exact prefixLift 3146709
  have htrace : WordTrace (prefixWord ++ tailWord_3146709) baseStart_3146709 baseEnd_3146709 := by
    simpa [prefixWord, tailWord_3146709, baseEnd_3146709] using wordTrace_append hprefix tailTrace_3146709
  have hstable : (prefixWord ++ tailWord_3146709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146709).length < 2 ^ (prefixWord ++ tailWord_3146709).sum := by decide
  have hdescent : baseEnd_3146709 < baseStart_3146709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146719 : List Nat := [1, 1, 2, 3, 5, 1, 2, 1, 3, 1, 3]
def baseStart_3146719 : Nat := 118140960795 + 3146719 * 2 ^ 59
def prefixEnd_3146719 : Nat := 4983230072969 + 3 ^ 40 * 3146719 * 2
def baseEnd_3146719 : Nat := 1615779331635379181141009

theorem tailTrace_3146719 : CollatzResearch.WordTrace tailWord_3146719 prefixEnd_3146719 1615779331635379181141009 := by
  unfold tailWord_3146719
  simp only [CollatzResearch.WordTrace]
  refine ⟨114770270686981954664371211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76513513791321303109580807 114770270686981954664371211)
  ·
    refine ⟨172155406030472931996556817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114770270686981954664371211 172155406030472931996556817)
    ·
      refine ⟨129116554522854698997417613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172155406030472931996556817 129116554522854698997417613)
      ·
        refine ⟨48418707946070512124031605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129116554522854698997417613 48418707946070512124031605)
        ·
          refine ⟨4539253869944110511627963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48418707946070512124031605 4539253869944110511627963)
          ·
            refine ⟨6808880804916165767441945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4539253869944110511627963 6808880804916165767441945)
            ·
              refine ⟨5106660603687124325581459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6808880804916165767441945 5106660603687124325581459)
              ·
                refine ⟨7659990905530686488372189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5106660603687124325581459 7659990905530686488372189)
                ·
                  refine ⟨2872496589574007433139571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7659990905530686488372189 2872496589574007433139571)
                  ·
                    refine ⟨4308744884361011149709357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2872496589574007433139571 4308744884361011149709357)
                    ·
                      refine ⟨1615779331635379181141009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4308744884361011149709357 1615779331635379181141009)
                      ·
                        rfl

theorem cell23_3146719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_3146719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146719 prefixEnd_3146719 := by exact prefixLift 3146719
  have htrace : WordTrace (prefixWord ++ tailWord_3146719) baseStart_3146719 baseEnd_3146719 := by
    simpa [prefixWord, tailWord_3146719, baseEnd_3146719] using wordTrace_append hprefix tailTrace_3146719
  have hstable : (prefixWord ++ tailWord_3146719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146719).length < 2 ^ (prefixWord ++ tailWord_3146719).sum := by decide
  have hdescent : baseEnd_3146719 < baseStart_3146719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146735 : List Nat := [1, 1, 2, 1, 4, 3, 3, 1, 1, 6]
def baseStart_3146735 : Nat := 118140960795 + 3146735 * 2 ^ 59
def prefixEnd_3146735 : Nat := 4983230072969 + 3 ^ 40 * 3146735 * 2
def baseEnd_3146735 : Nat := 538595849108617039513645

theorem tailTrace_3146735 : CollatzResearch.WordTrace tailWord_3146735 prefixEnd_3146735 538595849108617039513645 := by
  unfold tailWord_3146735
  simp only [CollatzResearch.WordTrace]
  refine ⟨114770854254923989396953659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76513902836615992931302439 114770854254923989396953659)
  ·
    refine ⟨172156281382385984095430489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114770854254923989396953659 172156281382385984095430489)
    ·
      refine ⟨129117211036789488071572867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172156281382385984095430489 129117211036789488071572867)
      ·
        refine ⟨193675816555184232107359301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129117211036789488071572867 193675816555184232107359301)
        ·
          refine ⟨36314215604097043520129869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193675816555184232107359301 36314215604097043520129869)
          ·
            refine ⟨13617830851536391320048701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36314215604097043520129869 13617830851536391320048701)
            ·
              refine ⟨5106686569326146745018263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13617830851536391320048701 5106686569326146745018263)
              ·
                refine ⟨7660029853989220117527395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5106686569326146745018263 7660029853989220117527395)
                ·
                  refine ⟨11490044780983830176291093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7660029853989220117527395 11490044780983830176291093)
                  ·
                    refine ⟨538595849108617039513645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11490044780983830176291093 538595849108617039513645)
                    ·
                      rfl

theorem cell23_3146735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 6].length) (baseStart_3146735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146735 prefixEnd_3146735 := by exact prefixLift 3146735
  have htrace : WordTrace (prefixWord ++ tailWord_3146735) baseStart_3146735 baseEnd_3146735 := by
    simpa [prefixWord, tailWord_3146735, baseEnd_3146735] using wordTrace_append hprefix tailTrace_3146735
  have hstable : (prefixWord ++ tailWord_3146735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146735).length < 2 ^ (prefixWord ++ tailWord_3146735).sum := by decide
  have hdescent : baseEnd_3146735 < baseStart_3146735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146762 : List Nat := [3, 1, 2, 2, 3, 2, 2, 1, 1, 1, 5]
def baseStart_3146762 : Nat := 118140960795 + 3146762 * 2 ^ 59
def prefixEnd_3146762 : Nat := 4983230072969 + 3 ^ 40 * 3146762 * 2
def baseEnd_3146762 : Nat := 1615801411303522512903311

theorem tailTrace_3146762 : CollatzResearch.WordTrace tailWord_3146762 prefixEnd_3146762 1615801411303522512903311 := by
  unfold tailWord_3146762
  simp only [CollatzResearch.WordTrace]
  refine ⟨28692959756456543252046635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76514559350550782005457693 28692959756456543252046635)
  ·
    refine ⟨43039439634684814878069953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28692959756456543252046635 43039439634684814878069953)
    ·
      refine ⟨32279579726013611158552465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43039439634684814878069953 32279579726013611158552465)
      ·
        refine ⟨24209684794510208368914349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32279579726013611158552465 24209684794510208368914349)
        ·
          refine ⟨9078631797941328138342881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24209684794510208368914349 9078631797941328138342881)
          ·
            refine ⟨6808973848455996103757161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9078631797941328138342881 6808973848455996103757161)
            ·
              refine ⟨5106730386341997077817871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6808973848455996103757161 5106730386341997077817871)
              ·
                refine ⟨7660095579512995616726807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5106730386341997077817871 7660095579512995616726807)
                ·
                  refine ⟨11490143369269493425090211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7660095579512995616726807 11490143369269493425090211)
                  ·
                    refine ⟨17235215053904240137635317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11490143369269493425090211 17235215053904240137635317)
                    ·
                      refine ⟨1615801411303522512903311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17235215053904240137635317 1615801411303522512903311)
                      ·
                        rfl

theorem cell23_3146762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_3146762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146762 prefixEnd_3146762 := by exact prefixLift 3146762
  have htrace : WordTrace (prefixWord ++ tailWord_3146762) baseStart_3146762 baseEnd_3146762 := by
    simpa [prefixWord, tailWord_3146762, baseEnd_3146762] using wordTrace_append hprefix tailTrace_3146762
  have hstable : (prefixWord ++ tailWord_3146762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146762).length < 2 ^ (prefixWord ++ tailWord_3146762).sum := by decide
  have hdescent : baseEnd_3146762 < baseStart_3146762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146768 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 6]
def baseStart_3146768 : Nat := 118140960795 + 3146768 * 2 ^ 59
def prefixEnd_3146768 : Nat := 4983230072969 + 3 ^ 40 * 3146768 * 2
def baseEnd_3146768 : Nat := 1615804492187449489428283

theorem tailTrace_3146768 : CollatzResearch.WordTrace tailWord_3146768 prefixEnd_3146768 1615804492187449489428283 := by
  unfold tailWord_3146768
  simp only [CollatzResearch.WordTrace]
  refine ⟨57386028931902218016452479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76514705242536290688603305 57386028931902218016452479)
  ·
    refine ⟨86079043397853327024678719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57386028931902218016452479 86079043397853327024678719)
    ·
      refine ⟨129118565096779990537018079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86079043397853327024678719 129118565096779990537018079)
      ·
        refine ⟨193677847645169985805527119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129118565096779990537018079 193677847645169985805527119)
        ·
          refine ⟨290516771467754978708290679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193677847645169985805527119 290516771467754978708290679)
          ·
            refine ⟨435775157201632468062436019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290516771467754978708290679 435775157201632468062436019)
            ·
              refine ⟨653662735802448702093654029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 435775157201632468062436019 653662735802448702093654029)
              ·
                refine ⟨245123525925918263285120261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 653662735802448702093654029 245123525925918263285120261)
                ·
                  refine ⟨45960661111109674365960049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 245123525925918263285120261 45960661111109674365960049)
                  ·
                    refine ⟨34470495833332255774470037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45960661111109674365960049 34470495833332255774470037)
                    ·
                      refine ⟨1615804492187449489428283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34470495833332255774470037 1615804492187449489428283)
                      ·
                        rfl

theorem cell23_3146768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 6].length) (baseStart_3146768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146768 prefixEnd_3146768 := by exact prefixLift 3146768
  have htrace : WordTrace (prefixWord ++ tailWord_3146768) baseStart_3146768 baseEnd_3146768 := by
    simpa [prefixWord, tailWord_3146768, baseEnd_3146768] using wordTrace_append hprefix tailTrace_3146768
  have hstable : (prefixWord ++ tailWord_3146768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146768).length < 2 ^ (prefixWord ++ tailWord_3146768).sum := by decide
  have hdescent : baseEnd_3146768 < baseStart_3146768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146770 : List Nat := [3, 2, 5, 1, 1, 2, 1, 1, 3, 1, 3]
def baseStart_3146770 : Nat := 118140960795 + 3146770 * 2 ^ 59
def prefixEnd_3146770 : Nat := 4983230072969 + 3 ^ 40 * 3146770 * 2
def baseEnd_3146770 : Nat := 1615805519148758481603275

theorem tailTrace_3146770 : CollatzResearch.WordTrace tailWord_3146770 prefixEnd_3146770 1615805519148758481603275 := by
  unfold tailWord_3146770
  simp only [CollatzResearch.WordTrace]
  refine ⟨28693032702449297593619441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76514753873198126916318509 28693032702449297593619441)
  ·
    refine ⟨21519774526836973195214581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28693032702449297593619441 21519774526836973195214581)
    ·
      refine ⟨2017478861890966237051367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21519774526836973195214581 2017478861890966237051367)
      ·
        refine ⟨3026218292836449355577051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2017478861890966237051367 3026218292836449355577051)
        ·
          refine ⟨4539327439254674033365577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3026218292836449355577051 4539327439254674033365577)
          ·
            refine ⟨3404495579441005525024183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4539327439254674033365577 3404495579441005525024183)
            ·
              refine ⟨5106743369161508287536275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3404495579441005525024183 5106743369161508287536275)
              ·
                refine ⟨7660115053742262431304413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5106743369161508287536275 7660115053742262431304413)
                ·
                  refine ⟨2872543145153348411739155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7660115053742262431304413 2872543145153348411739155)
                  ·
                    refine ⟨4308814717730022617608733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2872543145153348411739155 4308814717730022617608733)
                    ·
                      refine ⟨1615805519148758481603275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4308814717730022617608733 1615805519148758481603275)
                      ·
                        rfl

theorem cell23_3146770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_3146770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146770 prefixEnd_3146770 := by exact prefixLift 3146770
  have htrace : WordTrace (prefixWord ++ tailWord_3146770) baseStart_3146770 baseEnd_3146770 := by
    simpa [prefixWord, tailWord_3146770, baseEnd_3146770] using wordTrace_append hprefix tailTrace_3146770
  have hstable : (prefixWord ++ tailWord_3146770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146770).length < 2 ^ (prefixWord ++ tailWord_3146770).sum := by decide
  have hdescent : baseEnd_3146770 < baseStart_3146770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146776 : List Nat := [2, 1, 2, 3, 2, 4, 1, 1, 3, 2, 2]
def baseStart_3146776 : Nat := 118140960795 + 3146776 * 2 ^ 59
def prefixEnd_3146776 : Nat := 4983230072969 + 3 ^ 40 * 3146776 * 2
def baseEnd_3146776 : Nat := 1615808600032685458128247

theorem tailTrace_3146776 : CollatzResearch.WordTrace tailWord_3146776 prefixEnd_3146776 1615808600032685458128247 := by
  unfold tailWord_3146776
  simp only [CollatzResearch.WordTrace]
  refine ⟨57386174823887726699598091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76514899765183635599464121 57386174823887726699598091)
  ·
    refine ⟨86079262235831590049397137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57386174823887726699598091 86079262235831590049397137)
    ·
      refine ⟨64559446676873692537047853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86079262235831590049397137 64559446676873692537047853)
      ·
        refine ⟨24209792503827634701392945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64559446676873692537047853 24209792503827634701392945)
        ·
          refine ⟨18157344377870726026044709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24209792503827634701392945 18157344377870726026044709)
          ·
            refine ⟨3404502070850761129883383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18157344377870726026044709 3404502070850761129883383)
            ·
              refine ⟨5106753106276141694825075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3404502070850761129883383 5106753106276141694825075)
              ·
                refine ⟨7660129659414212542237613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5106753106276141694825075 7660129659414212542237613)
                ·
                  refine ⟨2872548622280329703339105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7660129659414212542237613 2872548622280329703339105)
                  ·
                    refine ⟨2154411466710247277504329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2872548622280329703339105 2154411466710247277504329)
                    ·
                      refine ⟨1615808600032685458128247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2154411466710247277504329 1615808600032685458128247)
                      ·
                        rfl

theorem cell23_3146776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_3146776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146776 prefixEnd_3146776 := by exact prefixLift 3146776
  have htrace : WordTrace (prefixWord ++ tailWord_3146776) baseStart_3146776 baseEnd_3146776 := by
    simpa [prefixWord, tailWord_3146776, baseEnd_3146776] using wordTrace_append hprefix tailTrace_3146776
  have hstable : (prefixWord ++ tailWord_3146776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146776).length < 2 ^ (prefixWord ++ tailWord_3146776).sum := by decide
  have hdescent : baseEnd_3146776 < baseStart_3146776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146786 : List Nat := [3, 3, 1, 1, 1, 5, 2, 1, 2, 4]
def baseStart_3146786 : Nat := 118140960795 + 3146786 * 2 ^ 59
def prefixEnd_3146786 : Nat := 4983230072969 + 3 ^ 40 * 3146786 * 2
def baseEnd_3146786 : Nat := 538604578279743473001067

theorem tailTrace_3146786 : CollatzResearch.WordTrace tailWord_3146786 prefixEnd_3146786 538604578279743473001067 := by
  unfold tailWord_3146786
  simp only [CollatzResearch.WordTrace]
  refine ⟨28693178594434806276765053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76515142918492816738040141 28693178594434806276765053)
  ·
    refine ⟨10759941972913052353786895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28693178594434806276765053 10759941972913052353786895)
    ·
      refine ⟨16139912959369578530680343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10759941972913052353786895 16139912959369578530680343)
      ·
        refine ⟨24209869439054367796020515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16139912959369578530680343 24209869439054367796020515)
        ·
          refine ⟨36314804158581551694030773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24209869439054367796020515 36314804158581551694030773)
          ·
            refine ⟨3404512889867020471315385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36314804158581551694030773 3404512889867020471315385)
            ·
              refine ⟨2553384667400265353486539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3404512889867020471315385 2553384667400265353486539)
              ·
                refine ⟨3830077001100398030229809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2553384667400265353486539 3830077001100398030229809)
                ·
                  refine ⟨2872557750825298522672357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3830077001100398030229809 2872557750825298522672357)
                  ·
                    refine ⟨538604578279743473001067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2872557750825298522672357 538604578279743473001067)
                    ·
                      rfl

theorem cell23_3146786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_3146786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146786 prefixEnd_3146786 := by exact prefixLift 3146786
  have htrace : WordTrace (prefixWord ++ tailWord_3146786) baseStart_3146786 baseEnd_3146786 := by
    simpa [prefixWord, tailWord_3146786, baseEnd_3146786] using wordTrace_append hprefix tailTrace_3146786
  have hstable : (prefixWord ++ tailWord_3146786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146786).length < 2 ^ (prefixWord ++ tailWord_3146786).sum := by decide
  have hdescent : baseEnd_3146786 < baseStart_3146786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146835 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 2, 4, 3]
def baseStart_3146835 : Nat := 118140960795 + 3146835 * 2 ^ 59
def prefixEnd_3146835 : Nat := 4983230072969 + 3 ^ 40 * 3146835 * 2
def baseEnd_3146835 : Nat := 1615838895391300727290475

theorem tailTrace_3146835 : CollatzResearch.WordTrace tailWord_3146835 prefixEnd_3146835 1615838895391300727290475 := by
  unfold tailWord_3146835
  simp only [CollatzResearch.WordTrace]
  refine ⟨114774501554561706475593959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76516334369707804317062639 114774501554561706475593959)
  ·
    refine ⟨172161752331842559713390939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114774501554561706475593959 172161752331842559713390939)
    ·
      refine ⟨258242628497763839570086409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172161752331842559713390939 258242628497763839570086409)
      ·
        refine ⟨193681971373322879677564807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258242628497763839570086409 193681971373322879677564807)
        ·
          refine ⟨290522957059984319516347211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193681971373322879677564807 290522957059984319516347211)
          ·
            refine ⟨435784435589976479274520817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290522957059984319516347211 435784435589976479274520817)
            ·
              refine ⟨326838326692482359455890613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435784435589976479274520817 326838326692482359455890613)
              ·
                refine ⟨30641093127420221198989745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 326838326692482359455890613 30641093127420221198989745)
                ·
                  refine ⟨22980819845565165899242309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30641093127420221198989745 22980819845565165899242309)
                  ·
                    refine ⟨4308903721043468606107933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22980819845565165899242309 4308903721043468606107933)
                    ·
                      refine ⟨1615838895391300727290475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4308903721043468606107933 1615838895391300727290475)
                      ·
                        rfl

theorem cell23_3146835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 4, 3].length) (baseStart_3146835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146835 prefixEnd_3146835 := by exact prefixLift 3146835
  have htrace : WordTrace (prefixWord ++ tailWord_3146835) baseStart_3146835 baseEnd_3146835 := by
    simpa [prefixWord, tailWord_3146835, baseEnd_3146835] using wordTrace_append hprefix tailTrace_3146835
  have hstable : (prefixWord ++ tailWord_3146835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146835).length < 2 ^ (prefixWord ++ tailWord_3146835).sum := by decide
  have hdescent : baseEnd_3146835 < baseStart_3146835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146855 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 9]
def baseStart_3146855 : Nat := 118140960795 + 3146855 * 2 ^ 59
def prefixEnd_3146855 : Nat := 4983230072969 + 3 ^ 40 * 3146855 * 2
def baseEnd_3146855 : Nat := 179538796111598961004487

theorem tailTrace_3146855 : CollatzResearch.WordTrace tailWord_3146855 prefixEnd_3146855 179538796111598961004487 := by
  unfold tailWord_3146855
  simp only [CollatzResearch.WordTrace]
  refine ⟨114775231014489249891322019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76516820676326166594214679 114775231014489249891322019)
  ·
    refine ⟨172162846521733874836983029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114775231014489249891322019 172162846521733874836983029)
    ·
      refine ⟨16140266861412550765967159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 172162846521733874836983029 16140266861412550765967159)
      ·
        refine ⟨24210400292118826148950739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16140266861412550765967159 24210400292118826148950739)
        ·
          refine ⟨36315600438178239223426109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24210400292118826148950739 36315600438178239223426109)
          ·
            refine ⟨13618350164316839708784791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36315600438178239223426109 13618350164316839708784791)
            ·
              refine ⟨20427525246475259563177187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13618350164316839708784791 20427525246475259563177187)
              ·
                refine ⟨30641287869712889344765781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20427525246475259563177187 30641287869712889344765781)
                ·
                  refine ⟨179538796111598961004487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30641287869712889344765781 179538796111598961004487)
                  ·
                    rfl

theorem cell23_3146855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 9].length) (baseStart_3146855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146855 prefixEnd_3146855 := by exact prefixLift 3146855
  have htrace : WordTrace (prefixWord ++ tailWord_3146855) baseStart_3146855 baseEnd_3146855 := by
    simpa [prefixWord, tailWord_3146855, baseEnd_3146855] using wordTrace_append hprefix tailTrace_3146855
  have hstable : (prefixWord ++ tailWord_3146855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146855).length < 2 ^ (prefixWord ++ tailWord_3146855).sum := by decide
  have hdescent : baseEnd_3146855 < baseStart_3146855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146872 : List Nat := [2, 1, 2, 1, 1, 1, 5, 5, 5]
def baseStart_3146872 : Nat := 118140960795 + 3146872 * 2 ^ 59
def prefixEnd_3146872 : Nat := 4983230072969 + 3 ^ 40 * 3146872 * 2
def baseEnd_3146872 : Nat := 179539766019501898058645

theorem tailTrace_3146872 : CollatzResearch.WordTrace tailWord_3146872 prefixEnd_3146872 179539766019501898058645 := by
  unfold tailWord_3146872
  simp only [CollatzResearch.WordTrace]
  refine ⟨57387925527713830897345435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76517234036951774529793913 57387925527713830897345435)
  ·
    refine ⟨86081888291570746346018153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57387925527713830897345435 86081888291570746346018153)
    ·
      refine ⟨64561416218678059759513615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86081888291570746346018153 64561416218678059759513615)
      ·
        refine ⟨96842124328017089639270423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64561416218678059759513615 96842124328017089639270423)
        ·
          refine ⟨145263186492025634458905635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96842124328017089639270423 145263186492025634458905635)
          ·
            refine ⟨217894779738038451688358453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145263186492025634458905635 217894779738038451688358453)
            ·
              refine ⟨20427635600441104845783605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 217894779738038451688358453 20427635600441104845783605)
              ·
                refine ⟨1915090837541353579292213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20427635600441104845783605 1915090837541353579292213)
                ·
                  refine ⟨179539766019501898058645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1915090837541353579292213 179539766019501898058645)
                  ·
                    rfl

theorem cell23_3146872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 5, 5].length) (baseStart_3146872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146872 prefixEnd_3146872 := by exact prefixLift 3146872
  have htrace : WordTrace (prefixWord ++ tailWord_3146872) baseStart_3146872 baseEnd_3146872 := by
    simpa [prefixWord, tailWord_3146872, baseEnd_3146872] using wordTrace_append hprefix tailTrace_3146872
  have hstable : (prefixWord ++ tailWord_3146872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146872).length < 2 ^ (prefixWord ++ tailWord_3146872).sum := by decide
  have hdescent : baseEnd_3146872 < baseStart_3146872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3146892 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 1, 7, 2]
def baseStart_3146892 : Nat := 118140960795 + 3146892 * 2 ^ 59
def prefixEnd_3146892 : Nat := 4983230072969 + 3 ^ 40 * 3146892 * 2
def baseEnd_3146892 : Nat := 1615868163788607004277713

theorem tailTrace_3146892 : CollatzResearch.WordTrace tailWord_3146892 prefixEnd_3146892 1615868163788607004277713 := by
  unfold tailWord_3146892
  simp only [CollatzResearch.WordTrace]
  refine ⟨57388290257677602605209465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76517720343570136806945953 57388290257677602605209465)
  ·
    refine ⟨43041217693258201953907099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57388290257677602605209465 43041217693258201953907099)
    ·
      refine ⟨64561826539887302930860649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43041217693258201953907099 64561826539887302930860649)
      ·
        refine ⟨48421369904915477198145487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64561826539887302930860649 48421369904915477198145487)
        ·
          refine ⟨72632054857373215797218231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48421369904915477198145487 72632054857373215797218231)
          ·
            refine ⟨108948082286059823695827347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72632054857373215797218231 108948082286059823695827347)
            ·
              refine ⟨163422123429089735543741021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108948082286059823695827347 163422123429089735543741021)
              ·
                refine ⟨61283296285908650828902883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163422123429089735543741021 61283296285908650828902883)
                ·
                  refine ⟨91924944428862976243354325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61283296285908650828902883 91924944428862976243354325)
                  ·
                    refine ⟨2154490885051476005703617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 91924944428862976243354325 2154490885051476005703617)
                    ·
                      refine ⟨1615868163788607004277713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2154490885051476005703617 1615868163788607004277713)
                      ·
                        rfl

theorem cell23_3146892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 7, 2].length) (baseStart_3146892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3146892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3146892 prefixEnd_3146892 := by exact prefixLift 3146892
  have htrace : WordTrace (prefixWord ++ tailWord_3146892) baseStart_3146892 baseEnd_3146892 := by
    simpa [prefixWord, tailWord_3146892, baseEnd_3146892] using wordTrace_append hprefix tailTrace_3146892
  have hstable : (prefixWord ++ tailWord_3146892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3146892).length < 2 ^ (prefixWord ++ tailWord_3146892).sum := by decide
  have hdescent : baseEnd_3146892 < baseStart_3146892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3146892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147029 : List Nat := [1, 3, 2, 1, 2, 1, 1, 6, 1, 1, 4]
def baseStart_3147029 : Nat := 118140960795 + 3147029 * 2 ^ 59
def prefixEnd_3147029 : Nat := 4983230072969 + 3 ^ 40 * 3147029 * 2
def baseEnd_3147029 : Nat := 1615938510638272968264583

theorem tailTrace_3147029 : CollatzResearch.WordTrace tailWord_3147029 prefixEnd_3147029 1615938510638272968264583 := by
  unfold tailWord_3147029
  simp only [CollatzResearch.WordTrace]
  refine ⟨114781577315858877608156141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76521051543905918405437427 114781577315858877608156141)
  ·
    refine ⟨43043091493447079103058553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114781577315858877608156141 43043091493447079103058553)
    ·
      refine ⟨32282318620085309327293915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43043091493447079103058553 32282318620085309327293915)
      ·
        refine ⟨48423477930127963990940873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32282318620085309327293915 48423477930127963990940873)
        ·
          refine ⟨36317608447595972993205655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48423477930127963990940873 36317608447595972993205655)
          ·
            refine ⟨54476412671393959489808483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36317608447595972993205655 54476412671393959489808483)
            ·
              refine ⟨81714619007090939234712725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54476412671393959489808483 81714619007090939234712725)
              ·
                refine ⟨3830372765957387776627159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81714619007090939234712725 3830372765957387776627159)
                ·
                  refine ⟨5745559148936081664940739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3830372765957387776627159 5745559148936081664940739)
                  ·
                    refine ⟨8618338723404122497411109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5745559148936081664940739 8618338723404122497411109)
                    ·
                      refine ⟨1615938510638272968264583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8618338723404122497411109 1615938510638272968264583)
                      ·
                        rfl

theorem cell23_3147029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_3147029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147029 prefixEnd_3147029 := by exact prefixLift 3147029
  have htrace : WordTrace (prefixWord ++ tailWord_3147029) baseStart_3147029 baseEnd_3147029 := by
    simpa [prefixWord, tailWord_3147029, baseEnd_3147029] using wordTrace_append hprefix tailTrace_3147029
  have hstable : (prefixWord ++ tailWord_3147029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147029).length < 2 ^ (prefixWord ++ tailWord_3147029).sum := by decide
  have hdescent : baseEnd_3147029 < baseStart_3147029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147040 : List Nat := [2, 1, 1, 5, 3, 1, 2, 3, 1, 1, 3]
def baseStart_3147040 : Nat := 118140960795 + 3147040 * 2 ^ 59
def prefixEnd_3147040 : Nat := 4983230072969 + 3 ^ 40 * 3147040 * 2
def baseEnd_3147040 : Nat := 1615944158925472425227033

theorem tailTrace_3147040 : CollatzResearch.WordTrace tailWord_3147040 prefixEnd_3147040 1615944158925472425227033 := by
  unfold tailWord_3147040
  simp only [CollatzResearch.WordTrace]
  refine ⟨57390989259409513243403287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76521319012546017657871049 57390989259409513243403287)
  ·
    refine ⟨86086483889114269865104931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57390989259409513243403287 86086483889114269865104931)
    ·
      refine ⟨129129725833671404797657397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86086483889114269865104931 129129725833671404797657397)
      ·
        refine ⟨12105911796906694199780381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 129129725833671404797657397 12105911796906694199780381)
        ·
          refine ⟨4539716923840010324917643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12105911796906694199780381 4539716923840010324917643)
          ·
            refine ⟨6809575385760015487376465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4539716923840010324917643 6809575385760015487376465)
            ·
              refine ⟨5107181539320011615532349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6809575385760015487376465 5107181539320011615532349)
              ·
                refine ⟨1915193077245004355824631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5107181539320011615532349 1915193077245004355824631)
                ·
                  refine ⟨2872789615867506533736947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1915193077245004355824631 2872789615867506533736947)
                  ·
                    refine ⟨4309184423801259800605421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2872789615867506533736947 4309184423801259800605421)
                    ·
                      refine ⟨1615944158925472425227033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4309184423801259800605421 1615944158925472425227033)
                      ·
                        rfl

theorem cell23_3147040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_3147040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147040 prefixEnd_3147040 := by exact prefixLift 3147040
  have htrace : WordTrace (prefixWord ++ tailWord_3147040) baseStart_3147040 baseEnd_3147040 := by
    simpa [prefixWord, tailWord_3147040, baseEnd_3147040] using wordTrace_append hprefix tailTrace_3147040
  have hstable : (prefixWord ++ tailWord_3147040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147040).length < 2 ^ (prefixWord ++ tailWord_3147040).sum := by decide
  have hdescent : baseEnd_3147040 < baseStart_3147040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147076 : List Nat := [2, 3, 4, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_3147076 : Nat := 118140960795 + 3147076 * 2 ^ 59
def prefixEnd_3147076 : Nat := 4983230072969 + 3 ^ 40 * 3147076 * 2
def baseEnd_3147076 : Nat := 1615962644229034284376867

theorem tailTrace_3147076 : CollatzResearch.WordTrace tailWord_3147076 prefixEnd_3147076 1615962644229034284376867 := by
  unfold tailWord_3147076
  simp only [CollatzResearch.WordTrace]
  refine ⟨57391645773344302317558541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76522194364459069756744721 57391645773344302317558541)
  ·
    refine ⟨21521867165004113369084453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57391645773344302317558541 21521867165004113369084453)
    ·
      refine ⟨4035350093438271256703335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21521867165004113369084453 4035350093438271256703335)
      ·
        refine ⟨6053025140157406885055003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4035350093438271256703335 6053025140157406885055003)
        ·
          refine ⟨9079537710236110327582505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6053025140157406885055003 9079537710236110327582505)
          ·
            refine ⟨6809653282677082745686879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9079537710236110327582505 6809653282677082745686879)
            ·
              refine ⟨10214479924015624118530319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6809653282677082745686879 10214479924015624118530319)
              ·
                refine ⟨15321719886023436177795479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10214479924015624118530319 15321719886023436177795479)
                ·
                  refine ⟨22982579829035154266693219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15321719886023436177795479 22982579829035154266693219)
                  ·
                    refine ⟨34473869743552731400039829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22982579829035154266693219 34473869743552731400039829)
                    ·
                      refine ⟨1615962644229034284376867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34473869743552731400039829 1615962644229034284376867)
                      ·
                        rfl

theorem cell23_3147076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_3147076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147076 prefixEnd_3147076 := by exact prefixLift 3147076
  have htrace : WordTrace (prefixWord ++ tailWord_3147076) baseStart_3147076 baseEnd_3147076 := by
    simpa [prefixWord, tailWord_3147076, baseEnd_3147076] using wordTrace_append hprefix tailTrace_3147076
  have hstable : (prefixWord ++ tailWord_3147076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147076).length < 2 ^ (prefixWord ++ tailWord_3147076).sum := by decide
  have hdescent : baseEnd_3147076 < baseStart_3147076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147082 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 2, 7]
def baseStart_3147082 : Nat := 118140960795 + 3147082 * 2 ^ 59
def prefixEnd_3147082 : Nat := 4983230072969 + 3 ^ 40 * 3147082 * 2
def baseEnd_3147082 : Nat := 538655241704320420300613

theorem tailTrace_3147082 : CollatzResearch.WordTrace tailWord_3147082 prefixEnd_3147082 538655241704320420300613 := by
  unfold tailWord_3147082
  simp only [CollatzResearch.WordTrace]
  refine ⟨28695877596166716914958875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76522340256444578439890333 28695877596166716914958875)
  ·
    refine ⟨43043816394250075372438313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28695877596166716914958875 43043816394250075372438313)
    ·
      refine ⟨32282862295687556529328735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43043816394250075372438313 32282862295687556529328735)
      ·
        refine ⟨48424293443531334793993103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32282862295687556529328735 48424293443531334793993103)
        ·
          refine ⟨72636440165297002190989655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48424293443531334793993103 72636440165297002190989655)
          ·
            refine ⟨108954660247945503286484483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72636440165297002190989655 108954660247945503286484483)
            ·
              refine ⟨163431990371918254929726725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108954660247945503286484483 163431990371918254929726725)
              ·
                refine ⟨30643498194734672799323761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163431990371918254929726725 30643498194734672799323761)
                ·
                  refine ⟨22982623646051004599492821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30643498194734672799323761 22982623646051004599492821)
                  ·
                    refine ⟨538655241704320420300613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22982623646051004599492821 538655241704320420300613)
                    ·
                      rfl

theorem cell23_3147082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_3147082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147082 prefixEnd_3147082 := by exact prefixLift 3147082
  have htrace : WordTrace (prefixWord ++ tailWord_3147082) baseStart_3147082 baseEnd_3147082 := by
    simpa [prefixWord, tailWord_3147082, baseEnd_3147082] using wordTrace_append hprefix tailTrace_3147082
  have hstable : (prefixWord ++ tailWord_3147082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147082).length < 2 ^ (prefixWord ++ tailWord_3147082).sum := by decide
  have hdescent : baseEnd_3147082 < baseStart_3147082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147114 : List Nat := [3, 1, 3, 3, 2, 1, 3, 2, 1, 2, 2]
def baseStart_3147114 : Nat := 118140960795 + 3147114 * 2 ^ 59
def prefixEnd_3147114 : Nat := 4983230072969 + 3 ^ 40 * 3147114 * 2
def baseEnd_3147114 : Nat := 1615982156493905135701693

theorem tailTrace_3147114 : CollatzResearch.WordTrace tailWord_3147114 prefixEnd_3147114 1615982156493905135701693 := by
  unfold tailWord_3147114
  simp only [CollatzResearch.WordTrace]
  refine ⟨28696169380137734281250099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76523118347033958083333597 28696169380137734281250099)
  ·
    refine ⟨43044254070206601421875149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28696169380137734281250099 43044254070206601421875149)
    ·
      refine ⟨16141595276327475533203181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43044254070206601421875149 16141595276327475533203181)
      ·
        refine ⟨6053098228622803324951193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16141595276327475533203181 6053098228622803324951193)
        ·
          refine ⟨4539823671467102493713395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6053098228622803324951193 4539823671467102493713395)
          ·
            refine ⟨6809735507200653740570093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4539823671467102493713395 6809735507200653740570093)
            ·
              refine ⟨2553650815200245152713785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6809735507200653740570093 2553650815200245152713785)
              ·
                refine ⟨1915238111400183864535339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2553650815200245152713785 1915238111400183864535339)
                ·
                  refine ⟨2872857167100275796803009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1915238111400183864535339 2872857167100275796803009)
                  ·
                    refine ⟨2154642875325206847602257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2872857167100275796803009 2154642875325206847602257)
                    ·
                      refine ⟨1615982156493905135701693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2154642875325206847602257 1615982156493905135701693)
                      ·
                        rfl

theorem cell23_3147114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_3147114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147114 prefixEnd_3147114 := by exact prefixLift 3147114
  have htrace : WordTrace (prefixWord ++ tailWord_3147114) baseStart_3147114 baseEnd_3147114 := by
    simpa [prefixWord, tailWord_3147114, baseEnd_3147114] using wordTrace_append hprefix tailTrace_3147114
  have hstable : (prefixWord ++ tailWord_3147114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147114).length < 2 ^ (prefixWord ++ tailWord_3147114).sum := by decide
  have hdescent : baseEnd_3147114 < baseStart_3147114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147134 : List Nat := [4, 2, 3, 2, 2, 1, 1, 2, 1, 2, 3]
def baseStart_3147134 : Nat := 118140960795 + 3147134 * 2 ^ 59
def prefixEnd_3147134 : Nat := 4983230072969 + 3 ^ 40 * 3147134 * 2
def baseEnd_3147134 : Nat := 1615992426106995057451601

theorem tailTrace_3147134 : CollatzResearch.WordTrace tailWord_3147134 prefixEnd_3147134 1615992426106995057451601 := by
  unfold tailWord_3147134
  simp only [CollatzResearch.WordTrace]
  refine ⟨14348175872559810067591057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76523604653652320360485637 14348175872559810067591057)
  ·
    refine ⟨10761131904419857550693293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14348175872559810067591057 10761131904419857550693293)
    ·
      refine ⟨4035424464157446581509985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10761131904419857550693293 4035424464157446581509985)
      ·
        refine ⟨3026568348118084936132489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4035424464157446581509985 3026568348118084936132489)
        ·
          refine ⟨2269926261088563702099367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3026568348118084936132489 2269926261088563702099367)
          ·
            refine ⟨3404889391632845553149051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2269926261088563702099367 3404889391632845553149051)
            ·
              refine ⟨5107334087449268329723577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3404889391632845553149051 5107334087449268329723577)
              ·
                refine ⟨3830500565586951247292683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5107334087449268329723577 3830500565586951247292683)
                ·
                  refine ⟨5745750848380426870939025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3830500565586951247292683 5745750848380426870939025)
                  ·
                    refine ⟨4309313136285320153204269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5745750848380426870939025 4309313136285320153204269)
                    ·
                      refine ⟨1615992426106995057451601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4309313136285320153204269 1615992426106995057451601)
                      ·
                        rfl

theorem cell23_3147134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_3147134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147134 prefixEnd_3147134 := by exact prefixLift 3147134
  have htrace : WordTrace (prefixWord ++ tailWord_3147134) baseStart_3147134 baseEnd_3147134 := by
    simpa [prefixWord, tailWord_3147134, baseEnd_3147134] using wordTrace_append hprefix tailTrace_3147134
  have hstable : (prefixWord ++ tailWord_3147134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147134).length < 2 ^ (prefixWord ++ tailWord_3147134).sum := by decide
  have hdescent : baseEnd_3147134 < baseStart_3147134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147139 : List Nat := [1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 5]
def baseStart_3147139 : Nat := 118140960795 + 3147139 * 2 ^ 59
def prefixEnd_3147139 : Nat := 4983230072969 + 3 ^ 40 * 3147139 * 2
def baseEnd_3147139 : Nat := 1615994993510267537889077

theorem tailTrace_3147139 : CollatzResearch.WordTrace tailWord_3147139 prefixEnd_3147139 1615994993510267537889077 := by
  unfold tailWord_3147139
  simp only [CollatzResearch.WordTrace]
  refine ⟨114785589345460366394660471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76523726230306910929773647 114785589345460366394660471)
  ·
    refine ⟨172178384018190549591990707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114785589345460366394660471 172178384018190549591990707)
    ·
      refine ⟨258267576027285824387986061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172178384018190549591990707 258267576027285824387986061)
      ·
        refine ⟨96850341010232184145494773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258267576027285824387986061 96850341010232184145494773)
        ·
          refine ⟨9079719469709267263640135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96850341010232184145494773 9079719469709267263640135)
          ·
            refine ⟨13619579204563900895460203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9079719469709267263640135 13619579204563900895460203)
            ·
              refine ⟨20429368806845851343190305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13619579204563900895460203 20429368806845851343190305)
              ·
                refine ⟨15322026605134388507392729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20429368806845851343190305 15322026605134388507392729)
                ·
                  refine ⟨11491519953850791380544547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15322026605134388507392729 11491519953850791380544547)
                  ·
                    refine ⟨17237279930776187070816821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11491519953850791380544547 17237279930776187070816821)
                    ·
                      refine ⟨1615994993510267537889077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17237279930776187070816821 1615994993510267537889077)
                      ·
                        rfl

theorem cell23_3147139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_3147139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147139 prefixEnd_3147139 := by exact prefixLift 3147139
  have htrace : WordTrace (prefixWord ++ tailWord_3147139) baseStart_3147139 baseEnd_3147139 := by
    simpa [prefixWord, tailWord_3147139, baseEnd_3147139] using wordTrace_append hprefix tailTrace_3147139
  have hstable : (prefixWord ++ tailWord_3147139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147139).length < 2 ^ (prefixWord ++ tailWord_3147139).sum := by decide
  have hdescent : baseEnd_3147139 < baseStart_3147139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147140 : List Nat := [2, 3, 2, 1, 1, 5, 1, 2, 1, 3, 2]
def baseStart_3147140 : Nat := 118140960795 + 3147140 * 2 ^ 59
def prefixEnd_3147140 : Nat := 4983230072969 + 3 ^ 40 * 3147140 * 2
def baseEnd_3147140 : Nat := 1615995506990922033976573

theorem tailTrace_3147140 : CollatzResearch.WordTrace tailWord_3147140 prefixEnd_3147140 1615995506990922033976573 := by
  unfold tailWord_3147140
  simp only [CollatzResearch.WordTrace]
  refine ⟨57392812909228371782723437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76523750545637829043631249 57392812909228371782723437)
  ·
    refine ⟨21522304840960639418521289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57392812909228371782723437 21522304840960639418521289)
    ·
      refine ⟨16141728630720479563890967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21522304840960639418521289 16141728630720479563890967)
      ·
        refine ⟨24212592946080719345836451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16141728630720479563890967 24212592946080719345836451)
        ·
          refine ⟨36318889419121079018754677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24212592946080719345836451 36318889419121079018754677)
          ·
            refine ⟨3404895883042601158008251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36318889419121079018754677 3404895883042601158008251)
            ·
              refine ⟨5107343824563901737012377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3404895883042601158008251 5107343824563901737012377)
              ·
                refine ⟨3830507868422926302759283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5107343824563901737012377 3830507868422926302759283)
                ·
                  refine ⟨5745761802634389454138925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3830507868422926302759283 5745761802634389454138925)
                  ·
                    refine ⟨2154660675987896045302097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5745761802634389454138925 2154660675987896045302097)
                    ·
                      refine ⟨1615995506990922033976573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2154660675987896045302097 1615995506990922033976573)
                      ·
                        rfl

theorem cell23_3147140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_3147140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147140 prefixEnd_3147140 := by exact prefixLift 3147140
  have htrace : WordTrace (prefixWord ++ tailWord_3147140) baseStart_3147140 baseEnd_3147140 := by
    simpa [prefixWord, tailWord_3147140, baseEnd_3147140] using wordTrace_append hprefix tailTrace_3147140
  have hstable : (prefixWord ++ tailWord_3147140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147140).length < 2 ^ (prefixWord ++ tailWord_3147140).sum := by decide
  have hdescent : baseEnd_3147140 < baseStart_3147140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147156 : List Nat := [2, 4, 2, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_3147156 : Nat := 118140960795 + 3147156 * 2 ^ 59
def prefixEnd_3147156 : Nat := 4983230072969 + 3 ^ 40 * 3147156 * 2
def baseEnd_3147156 : Nat := 1616003722681393971376499

theorem tailTrace_3147156 : CollatzResearch.WordTrace tailWord_3147156 prefixEnd_3147156 1616003722681393971376499 := by
  unfold tailWord_3147156
  simp only [CollatzResearch.WordTrace]
  refine ⟨57393104693199389149014661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76524139590932518865352881 57393104693199389149014661)
  ·
    refine ⟨10761207129974885465440249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57393104693199389149014661 10761207129974885465440249)
    ·
      refine ⟨8070905347481164099080187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10761207129974885465440249 8070905347481164099080187)
      ·
        refine ⟨12106358021221746148620281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8070905347481164099080187 12106358021221746148620281)
        ·
          refine ⟨9079768515916309611465211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12106358021221746148620281 9079768515916309611465211)
          ·
            refine ⟨13619652773874464417197817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9079768515916309611465211 13619652773874464417197817)
            ·
              refine ⟨10214739580405848312898363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13619652773874464417197817 10214739580405848312898363)
              ·
                refine ⟨15322109370608772469347545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10214739580405848312898363 15322109370608772469347545)
                ·
                  refine ⟨11491582027956579352010659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15322109370608772469347545 11491582027956579352010659)
                  ·
                    refine ⟨17237373041934869028015989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11491582027956579352010659 17237373041934869028015989)
                    ·
                      refine ⟨1616003722681393971376499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17237373041934869028015989 1616003722681393971376499)
                      ·
                        rfl

theorem cell23_3147156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_3147156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147156 prefixEnd_3147156 := by exact prefixLift 3147156
  have htrace : WordTrace (prefixWord ++ tailWord_3147156) baseStart_3147156 baseEnd_3147156 := by
    simpa [prefixWord, tailWord_3147156, baseEnd_3147156] using wordTrace_append hprefix tailTrace_3147156
  have hstable : (prefixWord ++ tailWord_3147156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147156).length < 2 ^ (prefixWord ++ tailWord_3147156).sum := by decide
  have hdescent : baseEnd_3147156 < baseStart_3147156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147170 : List Nat := [3, 3, 1, 2, 1, 2, 1, 4, 2, 2, 2]
def baseStart_3147170 : Nat := 118140960795 + 3147170 * 2 ^ 59
def prefixEnd_3147170 : Nat := 4983230072969 + 3 ^ 40 * 3147170 * 2
def baseEnd_3147170 : Nat := 1616010911410556916601435

theorem tailTrace_3147170 : CollatzResearch.WordTrace tailWord_3147170 prefixEnd_3147170 1616010911410556916601435 := by
  unfold tailWord_3147170
  simp only [CollatzResearch.WordTrace]
  refine ⟨28696680002087014672259741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76524480005565372459359309 28696680002087014672259741)
  ·
    refine ⟨10761255000782630502097403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28696680002087014672259741 10761255000782630502097403)
    ·
      refine ⟨16141882501173945753146105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10761255000782630502097403 16141882501173945753146105)
      ·
        refine ⟨12106411875880459314859579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16141882501173945753146105 12106411875880459314859579)
        ·
          refine ⟨18159617813820688972289369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12106411875880459314859579 18159617813820688972289369)
          ·
            refine ⟨13619713360365516729217027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18159617813820688972289369 13619713360365516729217027)
            ·
              refine ⟨20429570040548275093825541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13619713360365516729217027 20429570040548275093825541)
              ·
                refine ⟨3830544382602801580092289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20429570040548275093825541 3830544382602801580092289)
                ·
                  refine ⟨2872908286952101185069217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3830544382602801580092289 2872908286952101185069217)
                  ·
                    refine ⟨2154681215214075888801913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2872908286952101185069217 2154681215214075888801913)
                    ·
                      refine ⟨1616010911410556916601435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2154681215214075888801913 1616010911410556916601435)
                      ·
                        rfl

theorem cell23_3147170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_3147170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147170 prefixEnd_3147170 := by exact prefixLift 3147170
  have htrace : WordTrace (prefixWord ++ tailWord_3147170) baseStart_3147170 baseEnd_3147170 := by
    simpa [prefixWord, tailWord_3147170, baseEnd_3147170] using wordTrace_append hprefix tailTrace_3147170
  have hstable : (prefixWord ++ tailWord_3147170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147170).length < 2 ^ (prefixWord ++ tailWord_3147170).sum := by decide
  have hdescent : baseEnd_3147170 < baseStart_3147170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147246 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 3, 4, 3]
def baseStart_3147246 : Nat := 118140960795 + 3147246 * 2 ^ 59
def prefixEnd_3147246 : Nat := 4983230072969 + 3 ^ 40 * 3147246 * 2
def baseEnd_3147246 : Nat := 1616049935940298619251085

theorem tailTrace_3147246 : CollatzResearch.WordTrace tailWord_3147246 prefixEnd_3147246 1616049935940298619251085 := by
  unfold tailWord_3147246
  simp only [CollatzResearch.WordTrace]
  refine ⟨14348686494509090458600699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76526327970715149112537061 14348686494509090458600699)
  ·
    refine ⟨21523029741763635687901049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14348686494509090458600699 21523029741763635687901049)
    ·
      refine ⟨16142272306322726765925787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21523029741763635687901049 16142272306322726765925787)
      ·
        refine ⟨24213408459484090148888681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16142272306322726765925787 24213408459484090148888681)
        ·
          refine ⟨18160056344613067611666511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24213408459484090148888681 18160056344613067611666511)
          ·
            refine ⟨27240084516919601417499767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18160056344613067611666511 27240084516919601417499767)
            ·
              refine ⟨40860126775379402126249651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27240084516919601417499767 40860126775379402126249651)
              ·
                refine ⟨61290190163069103189374477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40860126775379402126249651 61290190163069103189374477)
                ·
                  refine ⟨22983821311150913696015429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61290190163069103189374477 22983821311150913696015429)
                  ·
                    refine ⟨4309466495840796318002893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22983821311150913696015429 4309466495840796318002893)
                    ·
                      refine ⟨1616049935940298619251085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4309466495840796318002893 1616049935940298619251085)
                      ·
                        rfl

theorem cell23_3147246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_3147246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147246 prefixEnd_3147246 := by exact prefixLift 3147246
  have htrace : WordTrace (prefixWord ++ tailWord_3147246) baseStart_3147246 baseEnd_3147246 := by
    simpa [prefixWord, tailWord_3147246, baseEnd_3147246] using wordTrace_append hprefix tailTrace_3147246
  have hstable : (prefixWord ++ tailWord_3147246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147246).length < 2 ^ (prefixWord ++ tailWord_3147246).sum := by decide
  have hdescent : baseEnd_3147246 < baseStart_3147246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147277 : List Nat := [1, 7, 1, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_3147277 : Nat := 118140960795 + 3147277 * 2 ^ 59
def prefixEnd_3147277 : Nat := 4983230072969 + 3 ^ 40 * 3147277 * 2
def baseEnd_3147277 : Nat := 1616065853840587997963443

theorem tailTrace_3147277 : CollatzResearch.WordTrace tailWord_3147277 prefixEnd_3147277 1616065853840587997963443 := by
  unfold tailWord_3147277
  simp only [CollatzResearch.WordTrace]
  refine ⟨114790622618960415963184085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76527081745973610642122723 114790622618960415963184085)
  ·
    refine ⟨2690405217631884749137127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 114790622618960415963184085 2690405217631884749137127)
    ·
      refine ⟨4035607826447827123705691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2690405217631884749137127 4035607826447827123705691)
      ·
        refine ⟨6053411739671740685558537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4035607826447827123705691 6053411739671740685558537)
        ·
          refine ⟨4540058804753805514168903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6053411739671740685558537 4540058804753805514168903)
          ·
            refine ⟨6810088207130708271253355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4540058804753805514168903 6810088207130708271253355)
            ·
              refine ⟨10215132310696062406880033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6810088207130708271253355 10215132310696062406880033)
              ·
                refine ⟨7661349233022046805160025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10215132310696062406880033 7661349233022046805160025)
                ·
                  refine ⟨5746011924766535103870019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7661349233022046805160025 5746011924766535103870019)
                  ·
                    refine ⟨8619017887149802655805029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5746011924766535103870019 8619017887149802655805029)
                    ·
                      refine ⟨1616065853840587997963443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8619017887149802655805029 1616065853840587997963443)
                      ·
                        rfl

theorem cell23_3147277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_3147277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147277 prefixEnd_3147277 := by exact prefixLift 3147277
  have htrace : WordTrace (prefixWord ++ tailWord_3147277) baseStart_3147277 baseEnd_3147277 := by
    simpa [prefixWord, tailWord_3147277, baseEnd_3147277] using wordTrace_append hprefix tailTrace_3147277
  have hstable : (prefixWord ++ tailWord_3147277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147277).length < 2 ^ (prefixWord ++ tailWord_3147277).sum := by decide
  have hdescent : baseEnd_3147277 < baseStart_3147277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147320 : List Nat := [2, 1, 2, 1, 4, 3, 2, 1, 2, 3, 2]
def baseStart_3147320 : Nat := 118140960795 + 3147320 * 2 ^ 59
def prefixEnd_3147320 : Nat := 4983230072969 + 3 ^ 40 * 3147320 * 2
def baseEnd_3147320 : Nat := 1616087933508731329725745

theorem tailTrace_3147320 : CollatzResearch.WordTrace tailWord_3147320 prefixEnd_3147320 1616087933508731329725745 := by
  unfold tailWord_3147320
  simp only [CollatzResearch.WordTrace]
  refine ⟨57396095478902317153499707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76528127305203089537999609 57396095478902317153499707)
  ·
    refine ⟨86094143218353475730249561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57396095478902317153499707 86094143218353475730249561)
    ·
      refine ⟨64570607413765106797687171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86094143218353475730249561 64570607413765106797687171)
      ·
        refine ⟨96855911120647660196530757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64570607413765106797687171 96855911120647660196530757)
        ·
          refine ⟨18160483335121436286849517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96855911120647660196530757 18160483335121436286849517)
          ·
            refine ⟨6810181250670538607568569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18160483335121436286849517 6810181250670538607568569)
            ·
              refine ⟨5107635938002903955676427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6810181250670538607568569 5107635938002903955676427)
              ·
                refine ⟨7661453907004355933514641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5107635938002903955676427 7661453907004355933514641)
                ·
                  refine ⟨5746090430253266950135981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7661453907004355933514641 5746090430253266950135981)
                  ·
                    refine ⟨2154783911344975106300993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5746090430253266950135981 2154783911344975106300993)
                    ·
                      refine ⟨1616087933508731329725745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2154783911344975106300993 1616087933508731329725745)
                      ·
                        rfl

theorem cell23_3147320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 2, 3, 2].length) (baseStart_3147320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147320 prefixEnd_3147320 := by exact prefixLift 3147320
  have htrace : WordTrace (prefixWord ++ tailWord_3147320) baseStart_3147320 baseEnd_3147320 := by
    simpa [prefixWord, tailWord_3147320, baseEnd_3147320] using wordTrace_append hprefix tailTrace_3147320
  have hstable : (prefixWord ++ tailWord_3147320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147320).length < 2 ^ (prefixWord ++ tailWord_3147320).sum := by decide
  have hdescent : baseEnd_3147320 < baseStart_3147320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147363 : List Nat := [1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 4]
def baseStart_3147363 : Nat := 118140960795 + 3147363 * 2 ^ 59
def prefixEnd_3147363 : Nat := 4983230072969 + 3 ^ 40 * 3147363 * 2
def baseEnd_3147363 : Nat := 1616110013176874661488047

theorem tailTrace_3147363 : CollatzResearch.WordTrace tailWord_3147363 prefixEnd_3147363 1616110013176874661488047 := by
  unfold tailWord_3147363
  simp only [CollatzResearch.WordTrace]
  refine ⟨114793759296648852650814743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76529172864432568433876495 114793759296648852650814743)
  ·
    refine ⟨172190638944973278976222115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114793759296648852650814743 172190638944973278976222115)
    ·
      refine ⟨258285958417459918464333173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172190638944973278976222115 258285958417459918464333173)
      ·
        refine ⟨24214308601636867356031235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 258285958417459918464333173 24214308601636867356031235)
        ·
          refine ⟨36321462902455301034046853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24214308601636867356031235 36321462902455301034046853)
          ·
            refine ⟨6810274294210368943883785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36321462902455301034046853 6810274294210368943883785)
            ·
              refine ⟨5107705720657776707912839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6810274294210368943883785 5107705720657776707912839)
              ·
                refine ⟨7661558580986665061869259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5107705720657776707912839 7661558580986665061869259)
                ·
                  refine ⟨11492337871479997592803889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7661558580986665061869259 11492337871479997592803889)
                  ·
                    refine ⟨8619253403609998194602917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11492337871479997592803889 8619253403609998194602917)
                    ·
                      refine ⟨1616110013176874661488047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8619253403609998194602917 1616110013176874661488047)
                      ·
                        rfl

theorem cell23_3147363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_3147363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147363 prefixEnd_3147363 := by exact prefixLift 3147363
  have htrace : WordTrace (prefixWord ++ tailWord_3147363) baseStart_3147363 baseEnd_3147363 := by
    simpa [prefixWord, tailWord_3147363, baseEnd_3147363] using wordTrace_append hprefix tailTrace_3147363
  have hstable : (prefixWord ++ tailWord_3147363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147363).length < 2 ^ (prefixWord ++ tailWord_3147363).sum := by decide
  have hdescent : baseEnd_3147363 < baseStart_3147363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147383 : List Nat := [1, 1, 3, 1, 1, 3, 1, 4, 4, 1, 3]
def baseStart_3147383 : Nat := 118140960795 + 3147383 * 2 ^ 59
def prefixEnd_3147383 : Nat := 4983230072969 + 3 ^ 40 * 3147383 * 2
def baseEnd_3147383 : Nat := 1616120282789964583237955

theorem tailTrace_3147383 : CollatzResearch.WordTrace tailWord_3147383 prefixEnd_3147383 1616120282789964583237955 := by
  unfold tailWord_3147383
  simp only [CollatzResearch.WordTrace]
  refine ⟨114794488756576396066542803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76529659171050930711028535 114794488756576396066542803)
  ·
    refine ⟨172191733134864594099814205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114794488756576396066542803 172191733134864594099814205)
    ·
      refine ⟨64571899925574222787430327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172191733134864594099814205 64571899925574222787430327)
      ·
        refine ⟨96857849888361334181145491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64571899925574222787430327 96857849888361334181145491)
        ·
          refine ⟨145286774832542001271718237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96857849888361334181145491 145286774832542001271718237)
          ·
            refine ⟨54482540562203250476894339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145286774832542001271718237 54482540562203250476894339)
            ·
              refine ⟨81723810843304875715341509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54482540562203250476894339 81723810843304875715341509)
              ·
                refine ⟨15323214533119664196626533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81723810843304875715341509 15323214533119664196626533)
                ·
                  refine ⟨2873102724959937036867475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15323214533119664196626533 2873102724959937036867475)
                  ·
                    refine ⟨4309654087439905555301213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2873102724959937036867475 4309654087439905555301213)
                    ·
                      refine ⟨1616120282789964583237955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4309654087439905555301213 1616120282789964583237955)
                      ·
                        rfl

theorem cell23_3147383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 4, 1, 3].length) (baseStart_3147383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147383 prefixEnd_3147383 := by exact prefixLift 3147383
  have htrace : WordTrace (prefixWord ++ tailWord_3147383) baseStart_3147383 baseEnd_3147383 := by
    simpa [prefixWord, tailWord_3147383, baseEnd_3147383] using wordTrace_append hprefix tailTrace_3147383
  have hstable : (prefixWord ++ tailWord_3147383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147383).length < 2 ^ (prefixWord ++ tailWord_3147383).sum := by decide
  have hdescent : baseEnd_3147383 < baseStart_3147383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147440 : List Nat := [2, 1, 1, 1, 2, 1, 5, 2, 4, 2, 2]
def baseStart_3147440 : Nat := 118140960795 + 3147440 * 2 ^ 59
def prefixEnd_3147440 : Nat := 4983230072969 + 3 ^ 40 * 3147440 * 2
def baseEnd_3147440 : Nat := 1616149551187270860225193

theorem tailTrace_3147440 : CollatzResearch.WordTrace tailWord_3147440 prefixEnd_3147440 1616149551187270860225193 := by
  unfold tailWord_3147440
  simp only [CollatzResearch.WordTrace]
  refine ⟨57398283858684947400683887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76531045144913263200911849 57398283858684947400683887)
  ·
    refine ⟨86097425788027421101025831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57398283858684947400683887 86097425788027421101025831)
    ·
      refine ⟨129146138682041131651538747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86097425788027421101025831 129146138682041131651538747)
      ·
        refine ⟨193719208023061697477308121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129146138682041131651538747 193719208023061697477308121)
        ·
          refine ⟨145289406017296273107981091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193719208023061697477308121 145289406017296273107981091)
          ·
            refine ⟨217934109025944409661971637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145289406017296273107981091 217934109025944409661971637)
            ·
              refine ⟨20431322721182288405809841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 217934109025944409661971637 20431322721182288405809841)
              ·
                refine ⟨15323492040886716304357381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20431322721182288405809841 15323492040886716304357381)
                ·
                  refine ⟨2873154757666259307067009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15323492040886716304357381 2873154757666259307067009)
                  ·
                    refine ⟨2154866068249694480300257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2873154757666259307067009 2154866068249694480300257)
                    ·
                      refine ⟨1616149551187270860225193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2154866068249694480300257 1616149551187270860225193)
                      ·
                        rfl

theorem cell23_3147440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 4, 2, 2].length) (baseStart_3147440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147440 prefixEnd_3147440 := by exact prefixLift 3147440
  have htrace : WordTrace (prefixWord ++ tailWord_3147440) baseStart_3147440 baseEnd_3147440 := by
    simpa [prefixWord, tailWord_3147440, baseEnd_3147440] using wordTrace_append hprefix tailTrace_3147440
  have hstable : (prefixWord ++ tailWord_3147440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147440).length < 2 ^ (prefixWord ++ tailWord_3147440).sum := by decide
  have hdescent : baseEnd_3147440 < baseStart_3147440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147456 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 7]
def baseStart_3147456 : Nat := 118140960795 + 3147456 * 2 ^ 59
def prefixEnd_3147456 : Nat := 4983230072969 + 3 ^ 40 * 3147456 * 2
def baseEnd_3147456 : Nat := 1616157766877742797625119

theorem tailTrace_3147456 : CollatzResearch.WordTrace tailWord_3147456 prefixEnd_3147456 1616157766877742797625119 := by
  unfold tailWord_3147456
  simp only [CollatzResearch.WordTrace]
  refine ⟨57398575642655964766975111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76531434190207953022633481 57398575642655964766975111)
  ·
    refine ⟨86097863463983947150462667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57398575642655964766975111 86097863463983947150462667)
    ·
      refine ⟨129146795195975920725694001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86097863463983947150462667 129146795195975920725694001)
      ·
        refine ⟨96860096396981940544270501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129146795195975920725694001 96860096396981940544270501)
        ·
          refine ⟨18161268074434113852050719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96860096396981940544270501 18161268074434113852050719)
          ·
            refine ⟨27241902111651170778076079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18161268074434113852050719 27241902111651170778076079)
            ·
              refine ⟨40862853167476756167114119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27241902111651170778076079 40862853167476756167114119)
              ·
                refine ⟨61294279751215134250671179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40862853167476756167114119 61294279751215134250671179)
                ·
                  refine ⟨91941419626822701376006769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61294279751215134250671179 91941419626822701376006769)
                  ·
                    refine ⟨68956064720117026032005077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91941419626822701376006769 68956064720117026032005077)
                    ·
                      refine ⟨1616157766877742797625119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68956064720117026032005077 1616157766877742797625119)
                      ·
                        rfl

theorem cell23_3147456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_3147456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147456 prefixEnd_3147456 := by exact prefixLift 3147456
  have htrace : WordTrace (prefixWord ++ tailWord_3147456) baseStart_3147456 baseEnd_3147456 := by
    simpa [prefixWord, tailWord_3147456, baseEnd_3147456] using wordTrace_append hprefix tailTrace_3147456
  have hstable : (prefixWord ++ tailWord_3147456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147456).length < 2 ^ (prefixWord ++ tailWord_3147456).sum := by decide
  have hdescent : baseEnd_3147456 < baseStart_3147456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147474 : List Nat := [3, 2, 2, 2, 2, 2, 1, 3, 2, 2, 2]
def baseStart_3147474 : Nat := 118140960795 + 3147474 * 2 ^ 59
def prefixEnd_3147474 : Nat := 4983230072969 + 3 ^ 40 * 3147474 * 2
def baseEnd_3147474 : Nat := 1616167009529523727200037

theorem tailTrace_3147474 : CollatzResearch.WordTrace tailWord_3147474 prefixEnd_3147474 1616167009529523727200037 := by
  unfold tailWord_3147474
  simp only [CollatzResearch.WordTrace]
  refine ⟨28699451949811679652026369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76531871866164479072070317 28699451949811679652026369)
  ·
    refine ⟨21524588962358759739019777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28699451949811679652026369 21524588962358759739019777)
    ·
      refine ⟨16143441721769069804264833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21524588962358759739019777 16143441721769069804264833)
      ·
        refine ⟨12107581291326802353198625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16143441721769069804264833 12107581291326802353198625)
        ·
          refine ⟨9080685968495101764898969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12107581291326802353198625 9080685968495101764898969)
          ·
            refine ⟨6810514476371326323674227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9080685968495101764898969 6810514476371326323674227)
            ·
              refine ⟨10215771714556989485511341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6810514476371326323674227 10215771714556989485511341)
              ·
                refine ⟨3830914392958871057066753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10215771714556989485511341 3830914392958871057066753)
                ·
                  refine ⟨2873185794719153292800065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3830914392958871057066753 2873185794719153292800065)
                  ·
                    refine ⟨2154889346039364969600049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2873185794719153292800065 2154889346039364969600049)
                    ·
                      refine ⟨1616167009529523727200037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2154889346039364969600049 1616167009529523727200037)
                      ·
                        rfl

theorem cell23_3147474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_3147474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147474 prefixEnd_3147474 := by exact prefixLift 3147474
  have htrace : WordTrace (prefixWord ++ tailWord_3147474) baseStart_3147474 baseEnd_3147474 := by
    simpa [prefixWord, tailWord_3147474, baseEnd_3147474] using wordTrace_append hprefix tailTrace_3147474
  have hstable : (prefixWord ++ tailWord_3147474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147474).length < 2 ^ (prefixWord ++ tailWord_3147474).sum := by decide
  have hdescent : baseEnd_3147474 < baseStart_3147474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147478 : List Nat := [5, 2, 1, 3, 1, 2, 1, 2, 1, 3, 2]
def baseStart_3147478 : Nat := 118140960795 + 3147478 * 2 ^ 59
def prefixEnd_3147478 : Nat := 4983230072969 + 3 ^ 40 * 3147478 * 2
def baseEnd_3147478 : Nat := 1616169063452141711550019

theorem tailTrace_3147478 : CollatzResearch.WordTrace tailWord_3147478 prefixEnd_3147478 1616169063452141711550019 := by
  unfold tailWord_3147478
  simp only [CollatzResearch.WordTrace]
  refine ⟨7174872105702014205703193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76531969127488151527500725 7174872105702014205703193)
  ·
    refine ⟨5381154079276510654277395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7174872105702014205703193 5381154079276510654277395)
    ·
      refine ⟨8071731118914765981416093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5381154079276510654277395 8071731118914765981416093)
      ·
        refine ⟨3026899169593037243031035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8071731118914765981416093 3026899169593037243031035)
        ·
          refine ⟨4540348754389555864546553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3026899169593037243031035 4540348754389555864546553)
          ·
            refine ⟨3405261565792166898409915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4540348754389555864546553 3405261565792166898409915)
            ·
              refine ⟨5107892348688250347614873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3405261565792166898409915 5107892348688250347614873)
              ·
                refine ⟨3830919261516187760711155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5107892348688250347614873 3830919261516187760711155)
                ·
                  refine ⟨5746378892274281641066733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3830919261516187760711155 5746378892274281641066733)
                  ·
                    refine ⟨2154892084602855615400025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5746378892274281641066733 2154892084602855615400025)
                    ·
                      refine ⟨1616169063452141711550019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2154892084602855615400025 1616169063452141711550019)
                      ·
                        rfl

theorem cell23_3147478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_3147478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147478 prefixEnd_3147478 := by exact prefixLift 3147478
  have htrace : WordTrace (prefixWord ++ tailWord_3147478) baseStart_3147478 baseEnd_3147478 := by
    simpa [prefixWord, tailWord_3147478, baseEnd_3147478] using wordTrace_append hprefix tailTrace_3147478
  have hstable : (prefixWord ++ tailWord_3147478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147478).length < 2 ^ (prefixWord ++ tailWord_3147478).sum := by decide
  have hdescent : baseEnd_3147478 < baseStart_3147478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147508 : List Nat := [2, 6, 1, 1, 1, 2, 2, 2, 2, 2, 2]
def baseStart_3147508 : Nat := 118140960795 + 3147508 * 2 ^ 59
def prefixEnd_3147508 : Nat := 4983230072969 + 3 ^ 40 * 3147508 * 2
def baseEnd_3147508 : Nat := 1616184467871776594174881

theorem tailTrace_3147508 : CollatzResearch.WordTrace tailWord_3147508 prefixEnd_3147508 1616184467871776594174881 := by
  unfold tailWord_3147508
  simp only [CollatzResearch.WordTrace]
  refine ⟨57399523940561771207421589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76532698587415694943228785 57399523940561771207421589)
  ·
    refine ⟨2690602684713833025347887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57399523940561771207421589 2690602684713833025347887)
    ·
      refine ⟨4035904027070749538021831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2690602684713833025347887 4035904027070749538021831)
      ·
        refine ⟨6053856040606124307032747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4035904027070749538021831 6053856040606124307032747)
        ·
          refine ⟨9080784060909186460549121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6053856040606124307032747 9080784060909186460549121)
          ·
            refine ⟨6810588045681889845411841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9080784060909186460549121 6810588045681889845411841)
            ·
              refine ⟨5107941034261417384058881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6810588045681889845411841 5107941034261417384058881)
              ·
                refine ⟨3830955775696063038044161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5107941034261417384058881 3830955775696063038044161)
                ·
                  refine ⟨2873216831772047278533121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3830955775696063038044161 2873216831772047278533121)
                  ·
                    refine ⟨2154912623829035458899841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2873216831772047278533121 2154912623829035458899841)
                    ·
                      refine ⟨1616184467871776594174881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2154912623829035458899841 1616184467871776594174881)
                      ·
                        rfl

theorem cell23_3147508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_3147508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147508 prefixEnd_3147508 := by exact prefixLift 3147508
  have htrace : WordTrace (prefixWord ++ tailWord_3147508) baseStart_3147508 baseEnd_3147508 := by
    simpa [prefixWord, tailWord_3147508, baseEnd_3147508] using wordTrace_append hprefix tailTrace_3147508
  have hstable : (prefixWord ++ tailWord_3147508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147508).length < 2 ^ (prefixWord ++ tailWord_3147508).sum := by decide
  have hdescent : baseEnd_3147508 < baseStart_3147508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147510 : List Nat := [5, 1, 1, 1, 1, 3, 2, 2, 2, 5]
def baseStart_3147510 : Nat := 118140960795 + 3147510 * 2 ^ 59
def prefixEnd_3147510 : Nat := 4983230072969 + 3 ^ 40 * 3147510 * 2
def baseEnd_3147510 : Nat := 538728498277695195449957

theorem tailTrace_3147510 : CollatzResearch.WordTrace tailWord_3147510 prefixEnd_3147510 538728498277695195449957 := by
  unfold tailWord_3147510
  simp only [CollatzResearch.WordTrace]
  refine ⟨7174945051694768547275999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76532747218077531170943989 7174945051694768547275999)
  ·
    refine ⟨10762417577542152820913999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7174945051694768547275999 10762417577542152820913999)
    ·
      refine ⟨16143626366313229231370999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10762417577542152820913999 16143626366313229231370999)
      ·
        refine ⟨24215439549469843847056499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16143626366313229231370999 24215439549469843847056499)
        ·
          refine ⟨36323159324204765770584749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24215439549469843847056499 36323159324204765770584749)
          ·
            refine ⟨13621184746576787163969281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36323159324204765770584749 13621184746576787163969281)
            ·
              refine ⟨10215888559932590372976961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13621184746576787163969281 10215888559932590372976961)
              ·
                refine ⟨7661916419949442779732721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10215888559932590372976961 7661916419949442779732721)
                ·
                  refine ⟨5746437314962082084799541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7661916419949442779732721 5746437314962082084799541)
                  ·
                    refine ⟨538728498277695195449957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5746437314962082084799541 538728498277695195449957)
                    ·
                      rfl

theorem cell23_3147510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_3147510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147510 prefixEnd_3147510 := by exact prefixLift 3147510
  have htrace : WordTrace (prefixWord ++ tailWord_3147510) baseStart_3147510 baseEnd_3147510 := by
    simpa [prefixWord, tailWord_3147510, baseEnd_3147510] using wordTrace_append hprefix tailTrace_3147510
  have hstable : (prefixWord ++ tailWord_3147510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147510).length < 2 ^ (prefixWord ++ tailWord_3147510).sum := by decide
  have hdescent : baseEnd_3147510 < baseStart_3147510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147530 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 1, 6, 2]
def baseStart_3147530 : Nat := 118140960795 + 3147530 * 2 ^ 59
def prefixEnd_3147530 : Nat := 4983230072969 + 3 ^ 40 * 3147530 * 2
def baseEnd_3147530 : Nat := 1616195764446175508099779

theorem tailTrace_3147530 : CollatzResearch.WordTrace tailWord_3147530 prefixEnd_3147530 1616195764446175508099779 := by
  unfold tailWord_3147530
  simp only [CollatzResearch.WordTrace]
  refine ⟨28699962571760960043036011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76533233524695893448096029 28699962571760960043036011)
  ·
    refine ⟨43049943857641440064554017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28699962571760960043036011 43049943857641440064554017)
    ·
      refine ⟨32287457893231080048415513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43049943857641440064554017 32287457893231080048415513)
      ·
        refine ⟨24215593419923310036311635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32287457893231080048415513 24215593419923310036311635)
        ·
          refine ⟨36323390129884965054467453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24215593419923310036311635 36323390129884965054467453)
          ·
            refine ⟨13621271298706861895425295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36323390129884965054467453 13621271298706861895425295)
            ·
              refine ⟨20431906948060292843137943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13621271298706861895425295 20431906948060292843137943)
              ·
                refine ⟨30647860422090439264706915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20431906948060292843137943 30647860422090439264706915)
                ·
                  refine ⟨45971790633135658897060373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30647860422090439264706915 45971790633135658897060373)
                  ·
                    refine ⟨2154927685928234010799705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45971790633135658897060373 2154927685928234010799705)
                    ·
                      refine ⟨1616195764446175508099779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2154927685928234010799705 1616195764446175508099779)
                      ·
                        rfl

theorem cell23_3147530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_3147530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147530 prefixEnd_3147530 := by exact prefixLift 3147530
  have htrace : WordTrace (prefixWord ++ tailWord_3147530) baseStart_3147530 baseEnd_3147530 := by
    simpa [prefixWord, tailWord_3147530, baseEnd_3147530] using wordTrace_append hprefix tailTrace_3147530
  have hstable : (prefixWord ++ tailWord_3147530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147530).length < 2 ^ (prefixWord ++ tailWord_3147530).sum := by decide
  have hdescent : baseEnd_3147530 < baseStart_3147530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147557 : List Nat := [1, 3, 1, 2, 3, 2, 1, 5, 1, 4]
def baseStart_3147557 : Nat := 118140960795 + 3147557 * 2 ^ 59
def prefixEnd_3147557 : Nat := 4983230072969 + 3 ^ 40 * 3147557 * 2
def baseEnd_3147557 : Nat := 538736542807948967487385

theorem tailTrace_3147557 : CollatzResearch.WordTrace tailWord_3147557 prefixEnd_3147557 538736542807948967487385 := by
  unfold tailWord_3147557
  simp only [CollatzResearch.WordTrace]
  refine ⟨114800835057946023783376925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76533890038630682522251283 114800835057946023783376925)
  ·
    refine ⟨43050313146729758918766347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114800835057946023783376925 43050313146729758918766347)
    ·
      refine ⟨64575469720094638378149521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43050313146729758918766347 64575469720094638378149521)
      ·
        refine ⟨48431602290070978783612141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64575469720094638378149521 48431602290070978783612141)
        ·
          refine ⟨18161850858776617043854553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48431602290070978783612141 18161850858776617043854553)
          ·
            refine ⟨13621388144082462782890915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18161850858776617043854553 13621388144082462782890915)
            ·
              refine ⟨20432082216123694174336373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13621388144082462782890915 20432082216123694174336373)
              ·
                refine ⟨1915507707761596328844035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20432082216123694174336373 1915507707761596328844035)
                ·
                  refine ⟨2873261561642394493266053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1915507707761596328844035 2873261561642394493266053)
                  ·
                    refine ⟨538736542807948967487385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2873261561642394493266053 538736542807948967487385)
                    ·
                      rfl

theorem cell23_3147557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 5, 1, 4].length) (baseStart_3147557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147557 prefixEnd_3147557 := by exact prefixLift 3147557
  have htrace : WordTrace (prefixWord ++ tailWord_3147557) baseStart_3147557 baseEnd_3147557 := by
    simpa [prefixWord, tailWord_3147557, baseEnd_3147557] using wordTrace_append hprefix tailTrace_3147557
  have hstable : (prefixWord ++ tailWord_3147557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147557).length < 2 ^ (prefixWord ++ tailWord_3147557).sum := by decide
  have hdescent : baseEnd_3147557 < baseStart_3147557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147570 : List Nat := [3, 2, 1, 1, 3, 2, 3, 2, 6]
def baseStart_3147570 : Nat := 118140960795 + 3147570 * 2 ^ 59
def prefixEnd_3147570 : Nat := 4983230072969 + 3 ^ 40 * 3147570 * 2
def baseEnd_3147570 : Nat := 179579589296928372399955

theorem tailTrace_3147570 : CollatzResearch.WordTrace tailWord_3147570 prefixEnd_3147570 179579589296928372399955 := by
  unfold tailWord_3147570
  simp only [CollatzResearch.WordTrace]
  refine ⟨28700327301724731750900041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76534206137932618002400109 28700327301724731750900041)
  ·
    refine ⟨21525245476293548813175031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28700327301724731750900041 21525245476293548813175031)
    ·
      refine ⟨32287868214440323219762547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21525245476293548813175031 32287868214440323219762547)
      ·
        refine ⟨48431802321660484829643821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32287868214440323219762547 48431802321660484829643821)
        ·
          refine ⟨18161925870622681811116433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48431802321660484829643821 18161925870622681811116433)
          ·
            refine ⟨13621444402967011358337325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18161925870622681811116433 13621444402967011358337325)
            ·
              refine ⟨5108041651112629259376497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13621444402967011358337325 5108041651112629259376497)
              ·
                refine ⟨3831031238334471944532373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5108041651112629259376497 3831031238334471944532373)
                ·
                  refine ⟨179579589296928372399955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3831031238334471944532373 179579589296928372399955)
                  ·
                    rfl

theorem cell23_3147570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 6].length) (baseStart_3147570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147570 prefixEnd_3147570 := by exact prefixLift 3147570
  have htrace : WordTrace (prefixWord ++ tailWord_3147570) baseStart_3147570 baseEnd_3147570 := by
    simpa [prefixWord, tailWord_3147570, baseEnd_3147570] using wordTrace_append hprefix tailTrace_3147570
  have hstable : (prefixWord ++ tailWord_3147570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147570).length < 2 ^ (prefixWord ++ tailWord_3147570).sum := by decide
  have hdescent : baseEnd_3147570 < baseStart_3147570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147574 : List Nat := [5, 1, 2, 2, 1, 2, 2, 1, 3, 4]
def baseStart_3147574 : Nat := 118140960795 + 3147574 * 2 ^ 59
def prefixEnd_3147574 : Nat := 4983230072969 + 3 ^ 40 * 3147574 * 2
def baseEnd_3147574 : Nat := 538739452531657778649859

theorem tailTrace_3147574 : CollatzResearch.WordTrace tailWord_3147574 prefixEnd_3147574 538739452531657778649859 := by
  unfold tailWord_3147574
  simp only [CollatzResearch.WordTrace]
  refine ⟨7175090943680277230421611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76534303399256290457830517 7175090943680277230421611)
  ·
    refine ⟨10762636415520415845632417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7175090943680277230421611 10762636415520415845632417)
    ·
      refine ⟨8071977311640311884224313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10762636415520415845632417 8071977311640311884224313)
      ·
        refine ⟨6053982983730233913168235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8071977311640311884224313 6053982983730233913168235)
        ·
          refine ⟨9080974475595350869752353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6053982983730233913168235 9080974475595350869752353)
          ·
            refine ⟨6810730856696513152314265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9080974475595350869752353 6810730856696513152314265)
            ·
              refine ⟨5108048142522384864235699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6810730856696513152314265 5108048142522384864235699)
              ·
                refine ⟨7662072213783577296353549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5108048142522384864235699 7662072213783577296353549)
                ·
                  refine ⟨2873277080168841486132581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7662072213783577296353549 2873277080168841486132581)
                  ·
                    refine ⟨538739452531657778649859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2873277080168841486132581 538739452531657778649859)
                    ·
                      rfl

theorem cell23_3147574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_3147574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147574 prefixEnd_3147574 := by exact prefixLift 3147574
  have htrace : WordTrace (prefixWord ++ tailWord_3147574) baseStart_3147574 baseEnd_3147574 := by
    simpa [prefixWord, tailWord_3147574, baseEnd_3147574] using wordTrace_append hprefix tailTrace_3147574
  have hstable : (prefixWord ++ tailWord_3147574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147574).length < 2 ^ (prefixWord ++ tailWord_3147574).sum := by decide
  have hdescent : baseEnd_3147574 < baseStart_3147574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147633 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 3, 1, 6]
def baseStart_3147633 : Nat := 118140960795 + 3147633 * 2 ^ 59
def prefixEnd_3147633 : Nat := 4983230072969 + 3 ^ 40 * 3147633 * 2
def baseEnd_3147633 : Nat := 1616248652953588605111805

theorem tailTrace_3147633 : CollatzResearch.WordTrace tailWord_3147633 prefixEnd_3147633 1616248652953588605111805 := by
  unfold tailWord_3147633
  simp only [CollatzResearch.WordTrace]
  refine ⟨114803607005670688763143553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76535738003780459175429035 114803607005670688763143553)
  ·
    refine ⟨86102705254253016572357665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114803607005670688763143553 86102705254253016572357665)
    ·
      refine ⟨64577028940689762429268249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86102705254253016572357665 64577028940689762429268249)
      ·
        refine ⟨48432771705517321821951187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64577028940689762429268249 48432771705517321821951187)
        ·
          refine ⟨72649157558275982732926781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48432771705517321821951187 72649157558275982732926781)
          ·
            refine ⟨27243434084353493524847543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72649157558275982732926781 27243434084353493524847543)
            ·
              refine ⟨40865151126530240287271315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27243434084353493524847543 40865151126530240287271315)
              ·
                refine ⟨61297726689795360430906973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40865151126530240287271315 61297726689795360430906973)
                ·
                  refine ⟨22986647508673260161590115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61297726689795360430906973 22986647508673260161590115)
                  ·
                    refine ⟨34479971263009890242385173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22986647508673260161590115 34479971263009890242385173)
                    ·
                      refine ⟨1616248652953588605111805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34479971263009890242385173 1616248652953588605111805)
                      ·
                        rfl

theorem cell23_3147633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_3147633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147633 prefixEnd_3147633 := by exact prefixLift 3147633
  have htrace : WordTrace (prefixWord ++ tailWord_3147633) baseStart_3147633 baseEnd_3147633 := by
    simpa [prefixWord, tailWord_3147633, baseEnd_3147633] using wordTrace_append hprefix tailTrace_3147633
  have hstable : (prefixWord ++ tailWord_3147633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147633).length < 2 ^ (prefixWord ++ tailWord_3147633).sum := by decide
  have hdescent : baseEnd_3147633 < baseStart_3147633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147727 : List Nat := [1, 1, 2, 1, 1, 5, 1, 4, 1, 4, 2]
def baseStart_3147727 : Nat := 118140960795 + 3147727 * 2 ^ 59
def prefixEnd_3147727 : Nat := 4983230072969 + 3 ^ 40 * 3147727 * 2
def baseEnd_3147727 : Nat := 1616296920135111237336373

theorem tailTrace_3147727 : CollatzResearch.WordTrace tailWord_3147727 prefixEnd_3147727 1616296920135111237336373 := by
  unfold tailWord_3147727
  simp only [CollatzResearch.WordTrace]
  refine ⟨114807035467330142817065435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76538023644886761878043623 114807035467330142817065435)
  ·
    refine ⟨172210553200995214225598153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114807035467330142817065435 172210553200995214225598153)
    ·
      refine ⟨129157914900746410669198615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172210553200995214225598153 129157914900746410669198615)
      ·
        refine ⟨193736872351119616003797923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129157914900746410669198615 193736872351119616003797923)
        ·
          refine ⟨290605308526679424005696885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193736872351119616003797923 290605308526679424005696885)
          ·
            refine ⟨27244247674376196000534083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 290605308526679424005696885 27244247674376196000534083)
            ·
              refine ⟨40866371511564294000801125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27244247674376196000534083 40866371511564294000801125)
              ·
                refine ⟨7662444658418305125150211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40866371511564294000801125 7662444658418305125150211)
                ·
                  refine ⟨11493666987627457687725317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7662444658418305125150211 11493666987627457687725317)
                  ·
                    refine ⟨2155062560180148316448497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11493666987627457687725317 2155062560180148316448497)
                    ·
                      refine ⟨1616296920135111237336373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2155062560180148316448497 1616296920135111237336373)
                      ·
                        rfl

theorem cell23_3147727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 4, 2].length) (baseStart_3147727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147727 prefixEnd_3147727 := by exact prefixLift 3147727
  have htrace : WordTrace (prefixWord ++ tailWord_3147727) baseStart_3147727 baseEnd_3147727 := by
    simpa [prefixWord, tailWord_3147727, baseEnd_3147727] using wordTrace_append hprefix tailTrace_3147727
  have hstable : (prefixWord ++ tailWord_3147727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147727).length < 2 ^ (prefixWord ++ tailWord_3147727).sum := by decide
  have hdescent : baseEnd_3147727 < baseStart_3147727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147738 : List Nat := [3, 1, 1, 2, 6, 1, 1, 2, 2, 1, 3]
def baseStart_3147738 : Nat := 118140960795 + 3147738 * 2 ^ 59
def prefixEnd_3147738 : Nat := 4983230072969 + 3 ^ 40 * 3147738 * 2
def baseEnd_3147738 : Nat := 1616302568422310694298823

theorem tailTrace_3147738 : CollatzResearch.WordTrace tailWord_3147738 prefixEnd_3147738 1616302568422310694298823 := by
  unfold tailWord_3147738
  simp only [CollatzResearch.WordTrace]
  refine ⟨28701859167572572923928967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76538291113526861130477245 28701859167572572923928967)
  ·
    refine ⟨43052788751358859385893451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28701859167572572923928967 43052788751358859385893451)
    ·
      refine ⟨64579183127038289078840177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43052788751358859385893451 64579183127038289078840177)
      ·
        refine ⟨48434387345278716809130133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64579183127038289078840177 48434387345278716809130133)
        ·
          refine ⟨2270361906809939850427975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48434387345278716809130133 2270361906809939850427975)
          ·
            refine ⟨3405542860214909775641963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2270361906809939850427975 3405542860214909775641963)
            ·
              refine ⟨5108314290322364663462945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3405542860214909775641963 5108314290322364663462945)
              ·
                refine ⟨3831235717741773497597209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5108314290322364663462945 3831235717741773497597209)
                ·
                  refine ⟨2873426788306330123197907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3831235717741773497597209 2873426788306330123197907)
                  ·
                    refine ⟨4310140182459495184796861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2873426788306330123197907 4310140182459495184796861)
                    ·
                      refine ⟨1616302568422310694298823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4310140182459495184796861 1616302568422310694298823)
                      ·
                        rfl

theorem cell23_3147738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 2, 1, 3].length) (baseStart_3147738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147738 prefixEnd_3147738 := by exact prefixLift 3147738
  have htrace : WordTrace (prefixWord ++ tailWord_3147738) baseStart_3147738 baseEnd_3147738 := by
    simpa [prefixWord, tailWord_3147738, baseEnd_3147738] using wordTrace_append hprefix tailTrace_3147738
  have hstable : (prefixWord ++ tailWord_3147738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147738).length < 2 ^ (prefixWord ++ tailWord_3147738).sum := by decide
  have hdescent : baseEnd_3147738 < baseStart_3147738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147761 : List Nat := [1, 2, 2, 2, 5, 2, 1, 1, 1, 4, 2]
def baseStart_3147761 : Nat := 118140960795 + 3147761 * 2 ^ 59
def prefixEnd_3147761 : Nat := 4983230072969 + 3 ^ 40 * 3147761 * 2
def baseEnd_3147761 : Nat := 1616314378477364104311217

theorem tailTrace_3147761 : CollatzResearch.WordTrace tailWord_3147761 prefixEnd_3147761 1616314378477364104311217 := by
  unfold tailWord_3147761
  simp only [CollatzResearch.WordTrace]
  refine ⟨114808275549206966623803137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76538850366137977749202091 114808275549206966623803137)
  ·
    refine ⟨86106206661905224967852353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114808275549206966623803137 86106206661905224967852353)
    ·
      refine ⟨64579654996428918725889265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86106206661905224967852353 64579654996428918725889265)
      ·
        refine ⟨48434741247321689044416949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64579654996428918725889265 48434741247321689044416949)
        ·
          refine ⟨4540756991936408347914089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48434741247321689044416949 4540756991936408347914089)
          ·
            refine ⟨3405567743952306260935567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4540756991936408347914089 3405567743952306260935567)
            ·
              refine ⟨5108351615928459391403351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3405567743952306260935567 5108351615928459391403351)
              ·
                refine ⟨7662527423892689087105027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5108351615928459391403351 7662527423892689087105027)
                ·
                  refine ⟨11493791135839033630657541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7662527423892689087105027 11493791135839033630657541)
                  ·
                    refine ⟨2155085837969818805748289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11493791135839033630657541 2155085837969818805748289)
                    ·
                      refine ⟨1616314378477364104311217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2155085837969818805748289 1616314378477364104311217)
                      ·
                        rfl

theorem cell23_3147761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 4, 2].length) (baseStart_3147761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147761 prefixEnd_3147761 := by exact prefixLift 3147761
  have htrace : WordTrace (prefixWord ++ tailWord_3147761) baseStart_3147761 baseEnd_3147761 := by
    simpa [prefixWord, tailWord_3147761, baseEnd_3147761] using wordTrace_append hprefix tailTrace_3147761
  have hstable : (prefixWord ++ tailWord_3147761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147761).length < 2 ^ (prefixWord ++ tailWord_3147761).sum := by decide
  have hdescent : baseEnd_3147761 < baseStart_3147761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147812 : List Nat := [2, 3, 1, 4, 3, 1, 2, 1, 2, 2, 2]
def baseStart_3147812 : Nat := 118140960795 + 3147812 * 2 ^ 59
def prefixEnd_3147812 : Nat := 4983230072969 + 3 ^ 40 * 3147812 * 2
def baseEnd_3147812 : Nat := 1616340565990743404773483

theorem tailTrace_3147812 : CollatzResearch.WordTrace tailWord_3147812 prefixEnd_3147812 1616340565990743404773483 := by
  unfold tailWord_3147812
  simp only [CollatzResearch.WordTrace]
  refine ⟨57405067836011101166954845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76540090448014801555939793 57405067836011101166954845)
  ·
    refine ⟨21526900438504162937608067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57405067836011101166954845 21526900438504162937608067)
    ·
      refine ⟨32290350657756244406412101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21526900438504162937608067 32290350657756244406412101)
      ·
        refine ⟨6054440748329295826202269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32290350657756244406412101 6054440748329295826202269)
        ·
          refine ⟨2270415280623485934825851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6054440748329295826202269 2270415280623485934825851)
          ·
            refine ⟨3405622920935228902238777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2270415280623485934825851 3405622920935228902238777)
            ·
              refine ⟨2554217190701421676679083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3405622920935228902238777 2554217190701421676679083)
              ·
                refine ⟨3831325786052132515018625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2554217190701421676679083 3831325786052132515018625)
                ·
                  refine ⟨2873494339539099386263969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3831325786052132515018625 2873494339539099386263969)
                  ·
                    refine ⟨2155120754654324539697977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2873494339539099386263969 2155120754654324539697977)
                    ·
                      refine ⟨1616340565990743404773483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2155120754654324539697977 1616340565990743404773483)
                      ·
                        rfl

theorem cell23_3147812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_3147812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147812 prefixEnd_3147812 := by exact prefixLift 3147812
  have htrace : WordTrace (prefixWord ++ tailWord_3147812) baseStart_3147812 baseEnd_3147812 := by
    simpa [prefixWord, tailWord_3147812, baseEnd_3147812] using wordTrace_append hprefix tailTrace_3147812
  have hstable : (prefixWord ++ tailWord_3147812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147812).length < 2 ^ (prefixWord ++ tailWord_3147812).sum := by decide
  have hdescent : baseEnd_3147812 < baseStart_3147812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147817 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 8, 4, 2]
def baseStart_3147817 : Nat := 118140960795 + 3147817 * 2 ^ 59
def prefixEnd_3147817 : Nat := 4983230072969 + 3 ^ 40 * 3147817 * 2
def baseEnd_3147817 : Nat := 1616343133394015885210959

theorem tailTrace_3147817 : CollatzResearch.WordTrace tailWord_3147817 prefixEnd_3147817 1616343133394015885210959 := by
  unfold tailWord_3147817
  simp only [CollatzResearch.WordTrace]
  refine ⟨114810318037004088187841705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76540212024669392125227803 114810318037004088187841705)
  ·
    refine ⟨86107738527753066140881279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114810318037004088187841705 86107738527753066140881279)
    ·
      refine ⟨129161607791629599211321919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86107738527753066140881279 129161607791629599211321919)
      ·
        refine ⟨193742411687444398816982879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129161607791629599211321919 193742411687444398816982879)
        ·
          refine ⟨290613617531166598225474319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193742411687444398816982879 290613617531166598225474319)
          ·
            refine ⟨435920426296749897338211479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290613617531166598225474319 435920426296749897338211479)
            ·
              refine ⟨653880639445124846007317219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 435920426296749897338211479 653880639445124846007317219)
              ·
                refine ⟨980820959167687269010975829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 653880639445124846007317219 980820959167687269010975829)
                ·
                  refine ⟨11493995615246335183722373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 980820959167687269010975829 11493995615246335183722373)
                  ·
                    refine ⟨2155124177858687846947945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11493995615246335183722373 2155124177858687846947945)
                    ·
                      refine ⟨1616343133394015885210959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2155124177858687846947945 1616343133394015885210959)
                      ·
                        rfl

theorem cell23_3147817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 4, 2].length) (baseStart_3147817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147817 prefixEnd_3147817 := by exact prefixLift 3147817
  have htrace : WordTrace (prefixWord ++ tailWord_3147817) baseStart_3147817 baseEnd_3147817 := by
    simpa [prefixWord, tailWord_3147817, baseEnd_3147817] using wordTrace_append hprefix tailTrace_3147817
  have hstable : (prefixWord ++ tailWord_3147817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147817).length < 2 ^ (prefixWord ++ tailWord_3147817).sum := by decide
  have hdescent : baseEnd_3147817 < baseStart_3147817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147827 : List Nat := [1, 1, 1, 2, 4, 1, 2, 4, 3, 4]
def baseStart_3147827 : Nat := 118140960795 + 3147827 * 2 ^ 59
def prefixEnd_3147827 : Nat := 4983230072969 + 3 ^ 40 * 3147827 * 2
def baseEnd_3147827 : Nat := 538782756066853615361971

theorem tailTrace_3147827 : CollatzResearch.WordTrace tailWord_3147827 prefixEnd_3147827 538782756066853615361971 := by
  unfold tailWord_3147827
  simp only [CollatzResearch.WordTrace]
  refine ⟨114810682766967859895705735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76540455177978573263803823 114810682766967859895705735)
  ·
    refine ⟨172216024150451789843558603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114810682766967859895705735 172216024150451789843558603)
    ·
      refine ⟨258324036225677684765337905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172216024150451789843558603 258324036225677684765337905)
      ·
        refine ⟨193743027169258263574003429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258324036225677684765337905 193743027169258263574003429)
        ·
          refine ⟨36326817594235924420125643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193743027169258263574003429 36326817594235924420125643)
          ·
            refine ⟨54490226391353886630188465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36326817594235924420125643 54490226391353886630188465)
            ·
              refine ⟨40867669793515414972641349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54490226391353886630188465 40867669793515414972641349)
              ·
                refine ⟨7662688086284140307370253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40867669793515414972641349 7662688086284140307370253)
                ·
                  refine ⟨2873508032356552615263845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7662688086284140307370253 2873508032356552615263845)
                  ·
                    refine ⟨538782756066853615361971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2873508032356552615263845 538782756066853615361971)
                    ·
                      rfl

theorem cell23_3147827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3, 4].length) (baseStart_3147827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147827 prefixEnd_3147827 := by exact prefixLift 3147827
  have htrace : WordTrace (prefixWord ++ tailWord_3147827) baseStart_3147827 baseEnd_3147827 := by
    simpa [prefixWord, tailWord_3147827, baseEnd_3147827] using wordTrace_append hprefix tailTrace_3147827
  have hstable : (prefixWord ++ tailWord_3147827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147827).length < 2 ^ (prefixWord ++ tailWord_3147827).sum := by decide
  have hdescent : baseEnd_3147827 < baseStart_3147827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147854 : List Nat := [4, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3]
def baseStart_3147854 : Nat := 118140960795 + 3147854 * 2 ^ 59
def prefixEnd_3147854 : Nat := 4983230072969 + 3 ^ 40 * 3147854 * 2
def baseEnd_3147854 : Nat := 1616362132178232240448289

theorem tailTrace_3147854 : CollatzResearch.WordTrace tailWord_3147854 prefixEnd_3147854 1616362132178232240448289 := by
  unfold tailWord_3147854
  simp only [CollatzResearch.WordTrace]
  refine ⟨14351458442233755438367327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76541111691913362337959077 14351458442233755438367327)
  ·
    refine ⟨21527187663350633157550991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14351458442233755438367327 21527187663350633157550991)
    ·
      refine ⟨32290781495025949736326487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21527187663350633157550991 32290781495025949736326487)
      ·
        refine ⟨48436172242538924604489731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32290781495025949736326487 48436172242538924604489731)
        ·
          refine ⟨72654258363808386906734597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48436172242538924604489731 72654258363808386906734597)
          ·
            refine ⟨13622673443214072545012737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72654258363808386906734597 13622673443214072545012737)
            ·
              refine ⟨10217005082410554408759553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13622673443214072545012737 10217005082410554408759553)
              ·
                refine ⟨7662753811807915806569665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10217005082410554408759553 7662753811807915806569665)
                ·
                  refine ⟨5747065358855936854927249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7662753811807915806569665 5747065358855936854927249)
                  ·
                    refine ⟨4310299019141952641195437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5747065358855936854927249 4310299019141952641195437)
                    ·
                      refine ⟨1616362132178232240448289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4310299019141952641195437 1616362132178232240448289)
                      ·
                        rfl

theorem cell23_3147854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_3147854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147854 prefixEnd_3147854 := by exact prefixLift 3147854
  have htrace : WordTrace (prefixWord ++ tailWord_3147854) baseStart_3147854 baseEnd_3147854 := by
    simpa [prefixWord, tailWord_3147854, baseEnd_3147854] using wordTrace_append hprefix tailTrace_3147854
  have hstable : (prefixWord ++ tailWord_3147854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147854).length < 2 ^ (prefixWord ++ tailWord_3147854).sum := by decide
  have hdescent : baseEnd_3147854 < baseStart_3147854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147861 : List Nat := [1, 3, 2, 2, 1, 4, 1, 4, 1, 4]
def baseStart_3147861 : Nat := 118140960795 + 3147861 * 2 ^ 59
def prefixEnd_3147861 : Nat := 4983230072969 + 3 ^ 40 * 3147861 * 2
def baseEnd_3147861 : Nat := 538788575514271237686919

theorem tailTrace_3147861 : CollatzResearch.WordTrace tailWord_3147861 prefixEnd_3147861 538788575514271237686919 := by
  unfold tailWord_3147861
  simp only [CollatzResearch.WordTrace]
  refine ⟨114811922848844683702443437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76541281899229789134962291 114811922848844683702443437)
  ·
    refine ⟨43054471068316756388416289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114811922848844683702443437 43054471068316756388416289)
    ·
      refine ⟨32290853301237567291312217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43054471068316756388416289 32290853301237567291312217)
      ·
        refine ⟨24218139975928175468484163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32290853301237567291312217 24218139975928175468484163)
        ·
          refine ⟨36327209963892263202726245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24218139975928175468484163 36327209963892263202726245)
          ·
            refine ⟨6811351868229799350511171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36327209963892263202726245 6811351868229799350511171)
            ·
              refine ⟨10217027802344699025766757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6811351868229799350511171 10217027802344699025766757)
              ·
                refine ⟨1915692712939631067331267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10217027802344699025766757 1915692712939631067331267)
                ·
                  refine ⟨2873539069409446600996901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1915692712939631067331267 2873539069409446600996901)
                  ·
                    refine ⟨538788575514271237686919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2873539069409446600996901 538788575514271237686919)
                    ·
                      rfl

theorem cell23_3147861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_3147861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147861 prefixEnd_3147861 := by exact prefixLift 3147861
  have htrace : WordTrace (prefixWord ++ tailWord_3147861) baseStart_3147861 baseEnd_3147861 := by
    simpa [prefixWord, tailWord_3147861, baseEnd_3147861] using wordTrace_append hprefix tailTrace_3147861
  have hstable : (prefixWord ++ tailWord_3147861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147861).length < 2 ^ (prefixWord ++ tailWord_3147861).sum := by decide
  have hdescent : baseEnd_3147861 < baseStart_3147861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147884 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 3]
def baseStart_3147884 : Nat := 118140960795 + 3147884 * 2 ^ 59
def prefixEnd_3147884 : Nat := 4983230072969 + 3 ^ 40 * 3147884 * 2
def baseEnd_3147884 : Nat := 1616377536597867123073151

theorem tailTrace_3147884 : CollatzResearch.WordTrace tailWord_3147884 prefixEnd_3147884 1616377536597867123073151 := by
  unfold tailWord_3147884
  simp only [CollatzResearch.WordTrace]
  refine ⟨57406380863880679315265353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76541841151840905753687137 57406380863880679315265353)
  ·
    refine ⟨43054785647910509486449015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57406380863880679315265353 43054785647910509486449015)
    ·
      refine ⟨64582178471865764229673523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43054785647910509486449015 64582178471865764229673523)
      ·
        refine ⟨96873267707798646344510285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64582178471865764229673523 96873267707798646344510285)
        ·
          refine ⟨36327475390424492379191357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96873267707798646344510285 36327475390424492379191357)
          ·
            refine ⟨13622803271409184642196759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36327475390424492379191357 13622803271409184642196759)
            ·
              refine ⟨20434204907113776963295139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13622803271409184642196759 20434204907113776963295139)
              ·
                refine ⟨30651307360670665444942709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20434204907113776963295139 30651307360670665444942709)
                ·
                  refine ⟨2873560065062874885463379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30651307360670665444942709 2873560065062874885463379)
                  ·
                    refine ⟨4310340097594312328195069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2873560065062874885463379 4310340097594312328195069)
                    ·
                      refine ⟨1616377536597867123073151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4310340097594312328195069 1616377536597867123073151)
                      ·
                        rfl

theorem cell23_3147884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 3].length) (baseStart_3147884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147884 prefixEnd_3147884 := by exact prefixLift 3147884
  have htrace : WordTrace (prefixWord ++ tailWord_3147884) baseStart_3147884 baseEnd_3147884 := by
    simpa [prefixWord, tailWord_3147884, baseEnd_3147884] using wordTrace_append hprefix tailTrace_3147884
  have hstable : (prefixWord ++ tailWord_3147884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147884).length < 2 ^ (prefixWord ++ tailWord_3147884).sum := by decide
  have hdescent : baseEnd_3147884 < baseStart_3147884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147887 : List Nat := [1, 1, 2, 1, 3, 4, 2, 1, 3, 5]
def baseStart_3147887 : Nat := 118140960795 + 3147887 * 2 ^ 59
def prefixEnd_3147887 : Nat := 4983230072969 + 3 ^ 40 * 3147887 * 2
def baseEnd_3147887 : Nat := 538793025679943537111879

theorem tailTrace_3147887 : CollatzResearch.WordTrace tailWord_3147887 prefixEnd_3147887 538793025679943537111879 := by
  unfold tailWord_3147887
  simp only [CollatzResearch.WordTrace]
  refine ⟨114812871146750490142889915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76541914097833660095259943 114812871146750490142889915)
  ·
    refine ⟨172219306720125735214334873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114812871146750490142889915 172219306720125735214334873)
    ·
      refine ⟨129164480040094301410751155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172219306720125735214334873 129164480040094301410751155)
      ·
        refine ⟨193746720060141452116126733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129164480040094301410751155 193746720060141452116126733)
        ·
          refine ⟨72655020022553044543547525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193746720060141452116126733 72655020022553044543547525)
          ·
            refine ⟨13622816254228695851915161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72655020022553044543547525 13622816254228695851915161)
            ·
              refine ⟨10217112190671521888936371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13622816254228695851915161 10217112190671521888936371)
              ·
                refine ⟨15325668286007282833404557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10217112190671521888936371 15325668286007282833404557)
                ·
                  refine ⟨5747125607252731062526709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15325668286007282833404557 5747125607252731062526709)
                  ·
                    refine ⟨538793025679943537111879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5747125607252731062526709 538793025679943537111879)
                    ·
                      rfl

theorem cell23_3147887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 5].length) (baseStart_3147887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147887 prefixEnd_3147887 := by exact prefixLift 3147887
  have htrace : WordTrace (prefixWord ++ tailWord_3147887) baseStart_3147887 baseEnd_3147887 := by
    simpa [prefixWord, tailWord_3147887, baseEnd_3147887] using wordTrace_append hprefix tailTrace_3147887
  have hstable : (prefixWord ++ tailWord_3147887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147887).length < 2 ^ (prefixWord ++ tailWord_3147887).sum := by decide
  have hdescent : baseEnd_3147887 < baseStart_3147887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147918 : List Nat := [4, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3]
def baseStart_3147918 : Nat := 118140960795 + 3147918 * 2 ^ 59
def prefixEnd_3147918 : Nat := 4983230072969 + 3 ^ 40 * 3147918 * 2
def baseEnd_3147918 : Nat := 1616394994940119990047995

theorem tailTrace_3147918 : CollatzResearch.WordTrace tailWord_3147918 prefixEnd_3147918 1616394994940119990047995 := by
  unfold tailWord_3147918
  simp only [CollatzResearch.WordTrace]
  refine ⟨14351750226204772804658551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76542667873092121624845605 14351750226204772804658551)
  ·
    refine ⟨21527625339307159206987827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14351750226204772804658551 21527625339307159206987827)
    ·
      refine ⟨32291438008960738810481741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21527625339307159206987827 32291438008960738810481741)
      ·
        refine ⟨12109289253360277053930653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32291438008960738810481741 12109289253360277053930653)
        ·
          refine ⟨4540983470010103895223995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12109289253360277053930653 4540983470010103895223995)
          ·
            refine ⟨6811475205015155842835993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4540983470010103895223995 6811475205015155842835993)
            ·
              refine ⟨5108606403761366882126995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6811475205015155842835993 5108606403761366882126995)
              ·
                refine ⟨7662909605642050323190493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5108606403761366882126995 7662909605642050323190493)
                ·
                  refine ⟨2873591102115768871196435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7662909605642050323190493 2873591102115768871196435)
                  ·
                    refine ⟨4310386653173653306794653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2873591102115768871196435 4310386653173653306794653)
                    ·
                      refine ⟨1616394994940119990047995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4310386653173653306794653 1616394994940119990047995)
                      ·
                        rfl

theorem cell23_3147918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_3147918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147918 prefixEnd_3147918 := by exact prefixLift 3147918
  have htrace : WordTrace (prefixWord ++ tailWord_3147918) baseStart_3147918 baseEnd_3147918 := by
    simpa [prefixWord, tailWord_3147918, baseEnd_3147918] using wordTrace_append hprefix tailTrace_3147918
  have hstable : (prefixWord ++ tailWord_3147918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147918).length < 2 ^ (prefixWord ++ tailWord_3147918).sum := by decide
  have hdescent : baseEnd_3147918 < baseStart_3147918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147941 : List Nat := [1, 3, 1, 2, 1, 3, 1, 4, 3, 2, 2]
def baseStart_3147941 : Nat := 118140960795 + 3147941 * 2 ^ 59
def prefixEnd_3147941 : Nat := 4983230072969 + 3 ^ 40 * 3147941 * 2
def baseEnd_3147941 : Nat := 1616406804995173400060389

theorem tailTrace_3147941 : CollatzResearch.WordTrace tailWord_3147941 prefixEnd_3147941 1616406804995173400060389 := by
  unfold tailWord_3147941
  simp only [CollatzResearch.WordTrace]
  refine ⟨114814840688554857365355677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76543227125703238243570451 114814840688554857365355677)
  ·
    refine ⟨43055565258208071512008379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114814840688554857365355677 43055565258208071512008379)
    ·
      refine ⟨64583347887312107268012569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43055565258208071512008379 64583347887312107268012569)
      ·
        refine ⟨48437510915484080451009427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64583347887312107268012569 48437510915484080451009427)
        ·
          refine ⟨72656266373226120676514141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48437510915484080451009427 72656266373226120676514141)
          ·
            refine ⟨27246099889959795253692803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72656266373226120676514141 27246099889959795253692803)
            ·
              refine ⟨40869149834939692880539205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27246099889959795253692803 40869149834939692880539205)
              ·
                refine ⟨7662965594051192415101101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40869149834939692880539205 7662965594051192415101101)
                ·
                  refine ⟨2873612097769197155662913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7662965594051192415101101 2873612097769197155662913)
                  ·
                    refine ⟨2155209073326897866747185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2873612097769197155662913 2155209073326897866747185)
                    ·
                      refine ⟨1616406804995173400060389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2155209073326897866747185 1616406804995173400060389)
                      ·
                        rfl

theorem cell23_3147941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 3, 2, 2].length) (baseStart_3147941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147941 prefixEnd_3147941 := by exact prefixLift 3147941
  have htrace : WordTrace (prefixWord ++ tailWord_3147941) baseStart_3147941 baseEnd_3147941 := by
    simpa [prefixWord, tailWord_3147941, baseEnd_3147941] using wordTrace_append hprefix tailTrace_3147941
  have hstable : (prefixWord ++ tailWord_3147941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147941).length < 2 ^ (prefixWord ++ tailWord_3147941).sum := by decide
  have hdescent : baseEnd_3147941 < baseStart_3147941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3147964 : List Nat := [2, 2, 2, 3, 3, 2, 9]
def baseStart_3147964 : Nat := 118140960795 + 3147964 * 2 ^ 59
def prefixEnd_3147964 : Nat := 4983230072969 + 3 ^ 40 * 3147964 * 2
def baseEnd_3147964 : Nat := 19955785370990454445343

theorem tailTrace_3147964 : CollatzResearch.WordTrace tailWord_3147964 prefixEnd_3147964 19955785370990454445343 := by
  unfold tailWord_3147964
  simp only [CollatzResearch.WordTrace]
  refine ⟨57407839783735766146721473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76543786378314354862295297 57407839783735766146721473)
  ·
    refine ⟨43055879837801824610041105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57407839783735766146721473 43055879837801824610041105)
    ·
      refine ⟨32291909878351368457530829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43055879837801824610041105 32291909878351368457530829)
      ·
        refine ⟨12109466204381763171574061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32291909878351368457530829 12109466204381763171574061)
        ·
          refine ⟨4541049826643161189340273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12109466204381763171574061 4541049826643161189340273)
          ·
            refine ⟨3405787369982370892005205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4541049826643161189340273 3405787369982370892005205)
            ·
              refine ⟨19955785370990454445343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3405787369982370892005205 19955785370990454445343)
              ·
                rfl

theorem cell23_3147964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 9].length) (baseStart_3147964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3147964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3147964 prefixEnd_3147964 := by exact prefixLift 3147964
  have htrace : WordTrace (prefixWord ++ tailWord_3147964) baseStart_3147964 baseEnd_3147964 := by
    simpa [prefixWord, tailWord_3147964, baseEnd_3147964] using wordTrace_append hprefix tailTrace_3147964
  have hstable : (prefixWord ++ tailWord_3147964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3147964).length < 2 ^ (prefixWord ++ tailWord_3147964).sum := by decide
  have hdescent : baseEnd_3147964 < baseStart_3147964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3147964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148001 : List Nat := [1, 2, 3, 1, 3, 1, 3, 1, 3, 3, 2]
def baseStart_3148001 : Nat := 118140960795 + 3148001 * 2 ^ 59
def prefixEnd_3148001 : Nat := 4983230072969 + 3 ^ 40 * 3148001 * 2
def baseEnd_3148001 : Nat := 1616437613834443165310113

theorem tailTrace_3148001 : CollatzResearch.WordTrace tailWord_3148001 prefixEnd_3148001 1616437613834443165310113 := by
  unfold tailWord_3148001
  simp only [CollatzResearch.WordTrace]
  refine ⟨114817029068337487612539857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76544686045558325075026571 114817029068337487612539857)
  ·
    refine ⟨86112771801253115709404893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114817029068337487612539857 86112771801253115709404893)
    ·
      refine ⟨32292289425469918391026835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86112771801253115709404893 32292289425469918391026835)
      ·
        refine ⟨48438434138204877586540253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32292289425469918391026835 48438434138204877586540253)
        ·
          refine ⟨18164412801826829094952595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48438434138204877586540253 18164412801826829094952595)
          ·
            refine ⟨27246619202740243642428893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18164412801826829094952595 27246619202740243642428893)
            ·
              refine ⟨10217482201027591365910835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27246619202740243642428893 10217482201027591365910835)
              ·
                refine ⟨15326223301541387048866253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10217482201027591365910835 15326223301541387048866253)
                ·
                  refine ⟨5747333738078020143324845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15326223301541387048866253 5747333738078020143324845)
                  ·
                    refine ⟨2155250151779257553746817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5747333738078020143324845 2155250151779257553746817)
                    ·
                      refine ⟨1616437613834443165310113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2155250151779257553746817 1616437613834443165310113)
                      ·
                        rfl

theorem cell23_3148001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 3, 2].length) (baseStart_3148001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148001 prefixEnd_3148001 := by exact prefixLift 3148001
  have htrace : WordTrace (prefixWord ++ tailWord_3148001) baseStart_3148001 baseEnd_3148001 := by
    simpa [prefixWord, tailWord_3148001, baseEnd_3148001] using wordTrace_append hprefix tailTrace_3148001
  have hstable : (prefixWord ++ tailWord_3148001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148001).length < 2 ^ (prefixWord ++ tailWord_3148001).sum := by decide
  have hdescent : baseEnd_3148001 < baseStart_3148001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148027 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 4]
def baseStart_3148027 : Nat := 118140960795 + 3148027 * 2 ^ 59
def prefixEnd_3148027 : Nat := 4983230072969 + 3 ^ 40 * 3148027 * 2
def baseEnd_3148027 : Nat := 1616450964331460063584993

theorem tailTrace_3148027 : CollatzResearch.WordTrace tailWord_3148027 prefixEnd_3148027 1616450964331460063584993 := by
  unfold tailWord_3148027
  simp only [CollatzResearch.WordTrace]
  refine ⟨114817977366243294052986335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76545318244162196035324223 114817977366243294052986335)
  ·
    refine ⟨172226966049364941079479503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114817977366243294052986335 172226966049364941079479503)
    ·
      refine ⟨258340449074047411619219255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172226966049364941079479503 258340449074047411619219255)
      ·
        refine ⟨387510673611071117428828883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258340449074047411619219255 387510673611071117428828883)
        ·
          refine ⟨581266010416606676143243325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387510673611071117428828883 581266010416606676143243325)
          ·
            refine ⟨217974753906227503553716247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 581266010416606676143243325 217974753906227503553716247)
            ·
              refine ⟨326962130859341255330574371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217974753906227503553716247 326962130859341255330574371)
              ·
                refine ⟨490443196289011882995861557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 326962130859341255330574371 490443196289011882995861557)
                ·
                  refine ⟨45979049652094864030862021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 490443196289011882995861557 45979049652094864030862021)
                  ·
                    refine ⟨8621071809767787005786629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45979049652094864030862021 8621071809767787005786629)
                    ·
                      refine ⟨1616450964331460063584993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8621071809767787005786629 1616450964331460063584993)
                      ·
                        rfl

theorem cell23_3148027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 4].length) (baseStart_3148027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148027 prefixEnd_3148027 := by exact prefixLift 3148027
  have htrace : WordTrace (prefixWord ++ tailWord_3148027) baseStart_3148027 baseEnd_3148027 := by
    simpa [prefixWord, tailWord_3148027, baseEnd_3148027] using wordTrace_append hprefix tailTrace_3148027
  have hstable : (prefixWord ++ tailWord_3148027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148027).length < 2 ^ (prefixWord ++ tailWord_3148027).sum := by decide
  have hdescent : baseEnd_3148027 < baseStart_3148027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148044 : List Nat := [2, 2, 1, 2, 2, 2, 3, 1, 2, 2, 4]
def baseStart_3148044 : Nat := 118140960795 + 3148044 * 2 ^ 59
def prefixEnd_3148044 : Nat := 4983230072969 + 3 ^ 40 * 3148044 * 2
def baseEnd_3148044 : Nat := 1616459693502586497072415

theorem tailTrace_3148044 : CollatzResearch.WordTrace tailWord_3148044 prefixEnd_3148044 1616459693502586497072415 := by
  unfold tailWord_3148044
  simp only [CollatzResearch.WordTrace]
  refine ⟨57409298703590852978177593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76545731604787803970903457 57409298703590852978177593)
  ·
    refine ⟨43056974027693139733633195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57409298703590852978177593 43056974027693139733633195)
    ·
      refine ⟨64585461041539709600449793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43056974027693139733633195 64585461041539709600449793)
      ·
        refine ⟨48439095781154782200337345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64585461041539709600449793 48439095781154782200337345)
        ·
          refine ⟨36329321835866086650253009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48439095781154782200337345 36329321835866086650253009)
          ·
            refine ⟨27246991376899564987689757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36329321835866086650253009 27246991376899564987689757)
            ·
              refine ⟨10217621766337336870383659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27246991376899564987689757 10217621766337336870383659)
              ·
                refine ⟨15326432649506005305575489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10217621766337336870383659 15326432649506005305575489)
                ·
                  refine ⟨11494824487129503979181617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15326432649506005305575489 11494824487129503979181617)
                  ·
                    refine ⟨8621118365347127984386213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11494824487129503979181617 8621118365347127984386213)
                    ·
                      refine ⟨1616459693502586497072415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8621118365347127984386213 1616459693502586497072415)
                      ·
                        rfl

theorem cell23_3148044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_3148044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148044 prefixEnd_3148044 := by exact prefixLift 3148044
  have htrace : WordTrace (prefixWord ++ tailWord_3148044) baseStart_3148044 baseEnd_3148044 := by
    simpa [prefixWord, tailWord_3148044, baseEnd_3148044] using wordTrace_append hprefix tailTrace_3148044
  have hstable : (prefixWord ++ tailWord_3148044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148044).length < 2 ^ (prefixWord ++ tailWord_3148044).sum := by decide
  have hdescent : baseEnd_3148044 < baseStart_3148044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148082 : List Nat := [3, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2]
def baseStart_3148082 : Nat := 118140960795 + 3148082 * 2 ^ 59
def prefixEnd_3148082 : Nat := 4983230072969 + 3 ^ 40 * 3148082 * 2
def baseEnd_3148082 : Nat := 1616479205767457348397241

theorem tailTrace_3148082 : CollatzResearch.WordTrace tailWord_3148082 prefixEnd_3148082 1616479205767457348397241 := by
  unfold tailWord_3148082
  simp only [CollatzResearch.WordTrace]
  refine ⟨28704995845261009611559625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76546655587362692297492333 28704995845261009611559625)
  ·
    refine ⟨21528746883945757208669719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28704995845261009611559625 21528746883945757208669719)
    ·
      refine ⟨32293120325918635813004579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21528746883945757208669719 32293120325918635813004579)
      ·
        refine ⟨48439680488877953719506869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32293120325918635813004579 48439680488877953719506869)
        ·
          refine ⟨4541220045832308161203769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48439680488877953719506869 4541220045832308161203769)
          ·
            refine ⟨3405915034374231120902827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4541220045832308161203769 3405915034374231120902827)
            ·
              refine ⟨5108872551561346681354241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3405915034374231120902827 5108872551561346681354241)
              ·
                refine ⟨3831654413671010011015681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5108872551561346681354241 3831654413671010011015681)
                ·
                  refine ⟨2873740810253257508261761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3831654413671010011015681 2873740810253257508261761)
                  ·
                    refine ⟨2155305607689943131196321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2873740810253257508261761 2155305607689943131196321)
                    ·
                      refine ⟨1616479205767457348397241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2155305607689943131196321 1616479205767457348397241)
                      ·
                        rfl

theorem cell23_3148082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2].length) (baseStart_3148082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148082 prefixEnd_3148082 := by exact prefixLift 3148082
  have htrace : WordTrace (prefixWord ++ tailWord_3148082) baseStart_3148082 baseEnd_3148082 := by
    simpa [prefixWord, tailWord_3148082, baseEnd_3148082] using wordTrace_append hprefix tailTrace_3148082
  have hstable : (prefixWord ++ tailWord_3148082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148082).length < 2 ^ (prefixWord ++ tailWord_3148082).sum := by decide
  have hdescent : baseEnd_3148082 < baseStart_3148082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148104 : List Nat := [2, 1, 3, 1, 1, 2, 3, 2, 1, 3, 4]
def baseStart_3148104 : Nat := 118140960795 + 3148104 * 2 ^ 59
def prefixEnd_3148104 : Nat := 4983230072969 + 3 ^ 40 * 3148104 * 2
def baseEnd_3148104 : Nat := 1616490502341856262322139

theorem tailTrace_3148104 : CollatzResearch.WordTrace tailWord_3148104 prefixEnd_3148104 1616490502341856262322139 := by
  unfold tailWord_3148104
  simp only [CollatzResearch.WordTrace]
  refine ⟨57410392893482168101769683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76547190524642890802359577 57410392893482168101769683)
  ·
    refine ⟨86115589340223252152654525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57410392893482168101769683 86115589340223252152654525)
    ·
      refine ⟨32293346002583719557245447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86115589340223252152654525 32293346002583719557245447)
      ·
        refine ⟨48440019003875579335868171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32293346002583719557245447 48440019003875579335868171)
        ·
          refine ⟨72660028505813369003802257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48440019003875579335868171 72660028505813369003802257)
          ·
            refine ⟨54495021379360026752851693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72660028505813369003802257 54495021379360026752851693)
            ·
              refine ⟨20435633017260010032319385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54495021379360026752851693 20435633017260010032319385)
              ·
                refine ⟨15326724762945007524239539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20435633017260010032319385 15326724762945007524239539)
                ·
                  refine ⟨22990087144417511286359309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15326724762945007524239539 22990087144417511286359309)
                  ·
                    refine ⟨8621282679156566732384741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22990087144417511286359309 8621282679156566732384741)
                    ·
                      refine ⟨1616490502341856262322139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8621282679156566732384741 1616490502341856262322139)
                      ·
                        rfl

theorem cell23_3148104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_3148104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148104 prefixEnd_3148104 := by exact prefixLift 3148104
  have htrace : WordTrace (prefixWord ++ tailWord_3148104) baseStart_3148104 baseEnd_3148104 := by
    simpa [prefixWord, tailWord_3148104, baseEnd_3148104] using wordTrace_append hprefix tailTrace_3148104
  have hstable : (prefixWord ++ tailWord_3148104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148104).length < 2 ^ (prefixWord ++ tailWord_3148104).sum := by decide
  have hdescent : baseEnd_3148104 < baseStart_3148104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148138 : List Nat := [3, 1, 3, 3, 1, 2, 1, 2, 2, 1, 4]
def baseStart_3148138 : Nat := 118140960795 + 3148138 * 2 ^ 59
def prefixEnd_3148138 : Nat := 4983230072969 + 3 ^ 40 * 3148138 * 2
def baseEnd_3148138 : Nat := 1616507960684109129296983

theorem tailTrace_3148138 : CollatzResearch.WordTrace tailWord_3148138 prefixEnd_3148138 1616507960684109129296983 := by
  unfold tailWord_3148138
  simp only [CollatzResearch.WordTrace]
  refine ⟨28705506467210290002569267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76548017245894106673518045 28705506467210290002569267)
  ·
    refine ⟨43058259700815435003853901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28705506467210290002569267 43058259700815435003853901)
    ·
      refine ⟨16146847387805788126445213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43058259700815435003853901 16146847387805788126445213)
      ·
        refine ⟨6055067770427170547416955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16146847387805788126445213 6055067770427170547416955)
        ·
          refine ⟨9082601655640755821125433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6055067770427170547416955 9082601655640755821125433)
          ·
            refine ⟨6811951241730566865844075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9082601655640755821125433 6811951241730566865844075)
            ·
              refine ⟨10217926862595850298766113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6811951241730566865844075 10217926862595850298766113)
              ·
                refine ⟨7663445146946887724074585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10217926862595850298766113 7663445146946887724074585)
                ·
                  refine ⟨5747583860210165793055939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7663445146946887724074585 5747583860210165793055939)
                  ·
                    refine ⟨8621375790315248689583909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5747583860210165793055939 8621375790315248689583909)
                    ·
                      refine ⟨1616507960684109129296983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8621375790315248689583909 1616507960684109129296983)
                      ·
                        rfl

theorem cell23_3148138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_3148138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148138 prefixEnd_3148138 := by exact prefixLift 3148138
  have htrace : WordTrace (prefixWord ++ tailWord_3148138) baseStart_3148138 baseEnd_3148138 := by
    simpa [prefixWord, tailWord_3148138, baseEnd_3148138] using wordTrace_append hprefix tailTrace_3148138
  have hstable : (prefixWord ++ tailWord_3148138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148138).length < 2 ^ (prefixWord ++ tailWord_3148138).sum := by decide
  have hdescent : baseEnd_3148138 < baseStart_3148138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148144 : List Nat := [2, 1, 1, 1, 4, 3, 2, 1, 8]
def baseStart_3148144 : Nat := 118140960795 + 3148144 * 2 ^ 59
def prefixEnd_3148144 : Nat := 4983230072969 + 3 ^ 40 * 3148144 * 2
def baseEnd_3148144 : Nat := 179612337952004011757995

theorem tailTrace_3148144 : CollatzResearch.WordTrace tailWord_3148144 prefixEnd_3148144 179612337952004011757995 := by
  unfold tailWord_3148144
  simp only [CollatzResearch.WordTrace]
  refine ⟨57411122353409711517497743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76548163137879615356663657 57411122353409711517497743)
  ·
    refine ⟨86116683530114567276246615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57411122353409711517497743 86116683530114567276246615)
    ·
      refine ⟨129175025295171850914369923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86116683530114567276246615 129175025295171850914369923)
      ·
        refine ⟨193762537942757776371554885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129175025295171850914369923 193762537942757776371554885)
        ·
          refine ⟨36330475864267083069666541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193762537942757776371554885 36330475864267083069666541)
          ·
            refine ⟨13623928449100156151124953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36330475864267083069666541 13623928449100156151124953)
            ·
              refine ⟨10217946336825117113343715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13623928449100156151124953 10217946336825117113343715)
              ·
                refine ⟨15326919505237675670015573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10217946336825117113343715 15326919505237675670015573)
                ·
                  refine ⟨179612337952004011757995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15326919505237675670015573 179612337952004011757995)
                  ·
                    rfl

theorem cell23_3148144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 8].length) (baseStart_3148144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148144 prefixEnd_3148144 := by exact prefixLift 3148144
  have htrace : WordTrace (prefixWord ++ tailWord_3148144) baseStart_3148144 baseEnd_3148144 := by
    simpa [prefixWord, tailWord_3148144, baseEnd_3148144] using wordTrace_append hprefix tailTrace_3148144
  have hstable : (prefixWord ++ tailWord_3148144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148144).length < 2 ^ (prefixWord ++ tailWord_3148144).sum := by decide
  have hdescent : baseEnd_3148144 < baseStart_3148144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148204 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 5, 6]
def baseStart_3148204 : Nat := 118140960795 + 3148204 * 2 ^ 59
def prefixEnd_3148204 : Nat := 4983230072969 + 3 ^ 40 * 3148204 * 2
def baseEnd_3148204 : Nat := 538847283469101957023893

theorem tailTrace_3148204 : CollatzResearch.WordTrace tailWord_3148204 prefixEnd_3148204 538847283469101957023893 := by
  unfold tailWord_3148204
  simp only [CollatzResearch.WordTrace]
  refine ⟨57412216543301026641089833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76549622057734702188119777 57412216543301026641089833)
  ·
    refine ⟨43059162407475769980817375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57412216543301026641089833 43059162407475769980817375)
    ·
      refine ⟨64588743611213654971226063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43059162407475769980817375 64588743611213654971226063)
      ·
        refine ⟨96883115416820482456839095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64588743611213654971226063 96883115416820482456839095)
        ·
          refine ⟨145324673125230723685258643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96883115416820482456839095 145324673125230723685258643)
          ·
            refine ⟨217987009687846085527887965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145324673125230723685258643 217987009687846085527887965)
            ·
              refine ⟨81745128632942282072957987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217987009687846085527887965 81745128632942282072957987)
              ·
                refine ⟨122617692949413423109436981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81745128632942282072957987 122617692949413423109436981)
                ·
                  refine ⟨11495408714007508416509717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122617692949413423109436981 11495408714007508416509717)
                  ·
                    refine ⟨538847283469101957023893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11495408714007508416509717 538847283469101957023893)
                    ·
                      rfl

theorem cell23_3148204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 6].length) (baseStart_3148204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148204 prefixEnd_3148204 := by exact prefixLift 3148204
  have htrace : WordTrace (prefixWord ++ tailWord_3148204) baseStart_3148204 baseEnd_3148204 := by
    simpa [prefixWord, tailWord_3148204, baseEnd_3148204] using wordTrace_append hprefix tailTrace_3148204
  have hstable : (prefixWord ++ tailWord_3148204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148204).length < 2 ^ (prefixWord ++ tailWord_3148204).sum := by decide
  have hdescent : baseEnd_3148204 < baseStart_3148204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148211 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 4, 6, 2]
def baseStart_3148211 : Nat := 118140960795 + 3148211 * 2 ^ 59
def prefixEnd_3148211 : Nat := 4983230072969 + 3 ^ 40 * 3148211 * 2
def baseEnd_3148211 : Nat := 1616545444771887343684147

theorem tailTrace_3148211 : CollatzResearch.WordTrace tailWord_3148211 prefixEnd_3148211 1616545444771887343684147 := by
  unfold tailWord_3148211
  simp only [CollatzResearch.WordTrace]
  refine ⟨114824688397576693477684487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76549792265051128985122991 114824688397576693477684487)
  ·
    refine ⟨172237032596365040216526731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114824688397576693477684487 172237032596365040216526731)
    ·
      refine ⟨258355548894547560324790097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172237032596365040216526731 258355548894547560324790097)
      ·
        refine ⟨193766661670910670243592573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258355548894547560324790097 193766661670910670243592573)
        ·
          refine ⟨72662498126591501341347215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193766661670910670243592573 72662498126591501341347215)
          ·
            refine ⟨108993747189887252012020823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72662498126591501341347215 108993747189887252012020823)
            ·
              refine ⟨163490620784830878018031235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108993747189887252012020823 163490620784830878018031235)
              ·
                refine ⟨245235931177246317027046853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163490620784830878018031235 245235931177246317027046853)
                ·
                  refine ⟨45981737095733684442571285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 245235931177246317027046853 45981737095733684442571285)
                  ·
                    refine ⟨2155393926362516458245529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45981737095733684442571285 2155393926362516458245529)
                    ·
                      refine ⟨1616545444771887343684147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2155393926362516458245529 1616545444771887343684147)
                      ·
                        rfl

theorem cell23_3148211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 6, 2].length) (baseStart_3148211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148211 prefixEnd_3148211 := by exact prefixLift 3148211
  have htrace : WordTrace (prefixWord ++ tailWord_3148211) baseStart_3148211 baseEnd_3148211 := by
    simpa [prefixWord, tailWord_3148211, baseEnd_3148211] using wordTrace_append hprefix tailTrace_3148211
  have hstable : (prefixWord ++ tailWord_3148211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148211).length < 2 ^ (prefixWord ++ tailWord_3148211).sum := by decide
  have hdescent : baseEnd_3148211 < baseStart_3148211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148221 : List Nat := [1, 4, 1, 2, 2, 2, 1, 3, 1, 6]
def baseStart_3148221 : Nat := 118140960795 + 3148221 * 2 ^ 59
def prefixEnd_3148221 : Nat := 4983230072969 + 3 ^ 40 * 3148221 * 2
def baseEnd_3148221 : Nat := 538850193192810768186367

theorem tailTrace_3148221 : CollatzResearch.WordTrace tailWord_3148221 prefixEnd_3148221 538850193192810768186367 := by
  unfold tailWord_3148221
  simp only [CollatzResearch.WordTrace]
  refine ⟨114825053127540465185548517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76550035418360310123699011 114825053127540465185548517)
  ·
    refine ⟨21529697461413837222290347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114825053127540465185548517 21529697461413837222290347)
    ·
      refine ⟨32294546192120755833435521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21529697461413837222290347 32294546192120755833435521)
      ·
        refine ⟨24220909644090566875076641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32294546192120755833435521 24220909644090566875076641)
        ·
          refine ⟨18165682233067925156307481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24220909644090566875076641 18165682233067925156307481)
          ·
            refine ⟨13624261674800943867230611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18165682233067925156307481 13624261674800943867230611)
            ·
              refine ⟨20436392512201415800845917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13624261674800943867230611 20436392512201415800845917)
              ·
                refine ⟨7663647192075530925317219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20436392512201415800845917 7663647192075530925317219)
                ·
                  refine ⟨11495470788113296387975829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7663647192075530925317219 11495470788113296387975829)
                  ·
                    refine ⟨538850193192810768186367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11495470788113296387975829 538850193192810768186367)
                    ·
                      rfl

theorem cell23_3148221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_3148221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148221 prefixEnd_3148221 := by exact prefixLift 3148221
  have htrace : WordTrace (prefixWord ++ tailWord_3148221) baseStart_3148221 baseEnd_3148221 := by
    simpa [prefixWord, tailWord_3148221, baseEnd_3148221] using wordTrace_append hprefix tailTrace_3148221
  have hstable : (prefixWord ++ tailWord_3148221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148221).length < 2 ^ (prefixWord ++ tailWord_3148221).sum := by decide
  have hdescent : baseEnd_3148221 < baseStart_3148221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148245 : List Nat := [1, 3, 2, 3, 1, 2, 4, 1, 1, 1, 4]
def baseStart_3148245 : Nat := 118140960795 + 3148245 * 2 ^ 59
def prefixEnd_3148245 : Nat := 4983230072969 + 3 ^ 40 * 3148245 * 2
def baseEnd_3148245 : Nat := 1616562903114140210658991

theorem tailTrace_3148245 : CollatzResearch.WordTrace tailWord_3148245 prefixEnd_3148245 1616562903114140210658991 := by
  unfold tailWord_3148245
  simp only [CollatzResearch.WordTrace]
  refine ⟨114825928479453517284422189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76550618986302344856281459 114825928479453517284422189)
  ·
    refine ⟨43059723179795068981658321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114825928479453517284422189 43059723179795068981658321)
    ·
      refine ⟨32294792384846301736243741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43059723179795068981658321 32294792384846301736243741)
      ·
        refine ⟨12110547144317363151091403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32294792384846301736243741 12110547144317363151091403)
        ·
          refine ⟨18165820716476044726637105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12110547144317363151091403 18165820716476044726637105)
          ·
            refine ⟨13624365537357033544977829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18165820716476044726637105 13624365537357033544977829)
            ·
              refine ⟨2554568538254443789683343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13624365537357033544977829 2554568538254443789683343)
              ·
                refine ⟨3831852807381665684525015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2554568538254443789683343 3831852807381665684525015)
                ·
                  refine ⟨5747779211072498526787523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3831852807381665684525015 5747779211072498526787523)
                  ·
                    refine ⟨8621668816608747790181285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5747779211072498526787523 8621668816608747790181285)
                    ·
                      refine ⟨1616562903114140210658991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8621668816608747790181285 1616562903114140210658991)
                      ·
                        rfl

theorem cell23_3148245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_3148245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148245 prefixEnd_3148245 := by exact prefixLift 3148245
  have htrace : WordTrace (prefixWord ++ tailWord_3148245) baseStart_3148245 baseEnd_3148245 := by
    simpa [prefixWord, tailWord_3148245, baseEnd_3148245] using wordTrace_append hprefix tailTrace_3148245
  have hstable : (prefixWord ++ tailWord_3148245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148245).length < 2 ^ (prefixWord ++ tailWord_3148245).sum := by decide
  have hdescent : baseEnd_3148245 < baseStart_3148245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148255 : List Nat := [1, 1, 2, 3, 3, 4, 1, 2, 2, 4]
def baseStart_3148255 : Nat := 118140960795 + 3148255 * 2 ^ 59
def prefixEnd_3148255 : Nat := 4983230072969 + 3 ^ 40 * 3148255 * 2
def baseEnd_3148255 : Nat := 538856012640228390511315

theorem tailTrace_3148255 : CollatzResearch.WordTrace tailWord_3148255 prefixEnd_3148255 538856012640228390511315 := by
  unfold tailWord_3148255
  simp only [CollatzResearch.WordTrace]
  refine ⟨114826293209417288992286219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76550862139611525994857479 114826293209417288992286219)
  ·
    refine ⟨172239439814125933488429329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114826293209417288992286219 172239439814125933488429329)
    ·
      refine ⟨129179579860594450116321997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172239439814125933488429329 129179579860594450116321997)
      ·
        refine ⟨48442342447722918793620749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129179579860594450116321997 48442342447722918793620749)
        ·
          refine ⟨18165878417896094547607781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48442342447722918793620749 18165878417896094547607781)
          ·
            refine ⟨3406102203355517727676459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18165878417896094547607781 3406102203355517727676459)
            ·
              refine ⟨5109153305033276591514689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3406102203355517727676459 5109153305033276591514689)
              ·
                refine ⟨3831864978774957443636017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5109153305033276591514689 3831864978774957443636017)
                ·
                  refine ⟨2873898734081218082727013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3831864978774957443636017 2873898734081218082727013)
                  ·
                    refine ⟨538856012640228390511315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2873898734081218082727013 538856012640228390511315)
                    ·
                      rfl

theorem cell23_3148255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 2, 4].length) (baseStart_3148255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148255 prefixEnd_3148255 := by exact prefixLift 3148255
  have htrace : WordTrace (prefixWord ++ tailWord_3148255) baseStart_3148255 baseEnd_3148255 := by
    simpa [prefixWord, tailWord_3148255, baseEnd_3148255] using wordTrace_append hprefix tailTrace_3148255
  have hstable : (prefixWord ++ tailWord_3148255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148255).length < 2 ^ (prefixWord ++ tailWord_3148255).sum := by decide
  have hdescent : baseEnd_3148255 < baseStart_3148255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148321 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 1, 3, 5]
def baseStart_3148321 : Nat := 118140960795 + 3148321 * 2 ^ 59
def prefixEnd_3148321 : Nat := 4983230072969 + 3 ^ 40 * 3148321 * 2
def baseEnd_3148321 : Nat := 1616601927643881913308641

theorem tailTrace_3148321 : CollatzResearch.WordTrace tailWord_3148321 prefixEnd_3148321 1616601927643881913308641 := by
  unfold tailWord_3148321
  simp only [CollatzResearch.WordTrace]
  refine ⟨114828700427178182264188817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76552466951452121509459211 114828700427178182264188817)
  ·
    refine ⟨86121525320383636698141613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114828700427178182264188817 86121525320383636698141613)
    ·
      refine ⟨32295571995143863761803105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86121525320383636698141613 32295571995143863761803105)
      ·
        refine ⟨24221678996357897821352329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32295571995143863761803105 24221678996357897821352329)
        ·
          refine ⟨18166259247268423366014247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24221678996357897821352329 18166259247268423366014247)
          ·
            refine ⟨27249388870902635049021371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18166259247268423366014247 27249388870902635049021371)
            ·
              refine ⟨40874083306353952573532057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27249388870902635049021371 40874083306353952573532057)
              ·
                refine ⟨30655562479765464430149043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40874083306353952573532057 30655562479765464430149043)
                ·
                  refine ⟨45983343719648196645223565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30655562479765464430149043 45983343719648196645223565)
                  ·
                    refine ⟨17243753894868073741958837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45983343719648196645223565 17243753894868073741958837)
                    ·
                      refine ⟨1616601927643881913308641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17243753894868073741958837 1616601927643881913308641)
                      ·
                        rfl

theorem cell23_3148321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_3148321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148321 prefixEnd_3148321 := by exact prefixLift 3148321
  have htrace : WordTrace (prefixWord ++ tailWord_3148321) baseStart_3148321 baseEnd_3148321 := by
    simpa [prefixWord, tailWord_3148321, baseEnd_3148321] using wordTrace_append hprefix tailTrace_3148321
  have hstable : (prefixWord ++ tailWord_3148321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148321).length < 2 ^ (prefixWord ++ tailWord_3148321).sum := by decide
  have hdescent : baseEnd_3148321 < baseStart_3148321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148331 : List Nat := [1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 4]
def baseStart_3148331 : Nat := 118140960795 + 3148331 * 2 ^ 59
def prefixEnd_3148331 : Nat := 4983230072969 + 3 ^ 40 * 3148331 * 2
def baseEnd_3148331 : Nat := 1616607062450426874183595

theorem tailTrace_3148331 : CollatzResearch.WordTrace tailWord_3148331 prefixEnd_3148331 1616607062450426874183595 := by
  unfold tailWord_3148331
  simp only [CollatzResearch.WordTrace]
  refine ⟨114829065157141953972052847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76552710104761302648035231 114829065157141953972052847)
  ·
    refine ⟨172243597735712930958079271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114829065157141953972052847 172243597735712930958079271)
    ·
      refine ⟨258365396603569396437118907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172243597735712930958079271 258365396603569396437118907)
      ·
        refine ⟨387548094905354094655678361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258365396603569396437118907 387548094905354094655678361)
        ·
          refine ⟨290661071179015570991758771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387548094905354094655678361 290661071179015570991758771)
          ·
            refine ⟨435991606768523356487638157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290661071179015570991758771 435991606768523356487638157)
            ·
              refine ⟨163496852538196258682864309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 435991606768523356487638157 163496852538196258682864309)
              ·
                refine ⟨15327829925455899251518529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 163496852538196258682864309 15327829925455899251518529)
                ·
                  refine ⟨11495872444091924438638897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15327829925455899251518529 11495872444091924438638897)
                  ·
                    refine ⟨8621904333068943328979173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11495872444091924438638897 8621904333068943328979173)
                    ·
                      refine ⟨1616607062450426874183595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8621904333068943328979173 1616607062450426874183595)
                      ·
                        rfl

theorem cell23_3148331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 4].length) (baseStart_3148331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148331 prefixEnd_3148331 := by exact prefixLift 3148331
  have htrace : WordTrace (prefixWord ++ tailWord_3148331) baseStart_3148331 baseEnd_3148331 := by
    simpa [prefixWord, tailWord_3148331, baseEnd_3148331] using wordTrace_append hprefix tailTrace_3148331
  have hstable : (prefixWord ++ tailWord_3148331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148331).length < 2 ^ (prefixWord ++ tailWord_3148331).sum := by decide
  have hdescent : baseEnd_3148331 < baseStart_3148331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148333 : List Nat := [1, 5, 4, 1, 2, 1, 1, 2, 1, 2, 3]
def baseStart_3148333 : Nat := 118140960795 + 3148333 * 2 ^ 59
def prefixEnd_3148333 : Nat := 4983230072969 + 3 ^ 40 * 3148333 * 2
def baseEnd_3148333 : Nat := 1616608089411735866358587

theorem tailTrace_3148333 : CollatzResearch.WordTrace tailWord_3148333 prefixEnd_3148333 1616608089411735866358587 := by
  unfold tailWord_3148333
  simp only [CollatzResearch.WordTrace]
  refine ⟨114829138103134708313625653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76552758735423138875750435 114829138103134708313625653)
  ·
    refine ⟨10765231697168878904402405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114829138103134708313625653 10765231697168878904402405)
    ·
      refine ⟨2018480943219164794575451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10765231697168878904402405 2018480943219164794575451)
      ·
        refine ⟨3027721414828747191863177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2018480943219164794575451 3027721414828747191863177)
        ·
          refine ⟨2270791061121560393897383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3027721414828747191863177 2270791061121560393897383)
          ·
            refine ⟨3406186591682340590846075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2270791061121560393897383 3406186591682340590846075)
            ·
              refine ⟨5109279887523510886269113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3406186591682340590846075 5109279887523510886269113)
              ·
                refine ⟨3831959915642633164701835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5109279887523510886269113 3831959915642633164701835)
                ·
                  refine ⟨5747939873463949747052753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3831959915642633164701835 5747939873463949747052753)
                  ·
                    refine ⟨4310954905097962310289565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5747939873463949747052753 4310954905097962310289565)
                    ·
                      refine ⟨1616608089411735866358587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4310954905097962310289565 1616608089411735866358587)
                      ·
                        rfl

theorem cell23_3148333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_3148333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148333 prefixEnd_3148333 := by exact prefixLift 3148333
  have htrace : WordTrace (prefixWord ++ tailWord_3148333) baseStart_3148333 baseEnd_3148333 := by
    simpa [prefixWord, tailWord_3148333, baseEnd_3148333] using wordTrace_append hprefix tailTrace_3148333
  have hstable : (prefixWord ++ tailWord_3148333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148333).length < 2 ^ (prefixWord ++ tailWord_3148333).sum := by decide
  have hdescent : baseEnd_3148333 < baseStart_3148333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148341 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 9]
def baseStart_3148341 : Nat := 118140960795 + 3148341 * 2 ^ 59
def prefixEnd_3148341 : Nat := 4983230072969 + 3 ^ 40 * 3148341 * 2
def baseEnd_3148341 : Nat := 179623577472996870562061

theorem tailTrace_3148341 : CollatzResearch.WordTrace tailWord_3148341 prefixEnd_3148341 179623577472996870562061 := by
  unfold tailWord_3148341
  simp only [CollatzResearch.WordTrace]
  refine ⟨114829429887105725679916877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76552953258070483786611251 114829429887105725679916877)
  ·
    refine ⟨43061036207664647129968829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114829429887105725679916877 43061036207664647129968829)
    ·
      refine ⟨16147888577874242673738311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43061036207664647129968829 16147888577874242673738311)
      ·
        refine ⟨24221832866811364010607467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16147888577874242673738311 24221832866811364010607467)
        ·
          refine ⟨36332749300217046015911201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24221832866811364010607467 36332749300217046015911201)
          ·
            refine ⟨27249561975162784511933401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36332749300217046015911201 27249561975162784511933401)
            ·
              refine ⟨20437171481372088383950051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27249561975162784511933401 20437171481372088383950051)
              ·
                refine ⟨30655757222058132575925077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20437171481372088383950051 30655757222058132575925077)
                ·
                  refine ⟨179623577472996870562061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30655757222058132575925077 179623577472996870562061)
                  ·
                    rfl

theorem cell23_3148341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 9].length) (baseStart_3148341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148341 prefixEnd_3148341 := by exact prefixLift 3148341
  have htrace : WordTrace (prefixWord ++ tailWord_3148341) baseStart_3148341 baseEnd_3148341 := by
    simpa [prefixWord, tailWord_3148341, baseEnd_3148341] using wordTrace_append hprefix tailTrace_3148341
  have hstable : (prefixWord ++ tailWord_3148341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148341).length < 2 ^ (prefixWord ++ tailWord_3148341).sum := by decide
  have hdescent : baseEnd_3148341 < baseStart_3148341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148405 : List Nat := [1, 3, 4, 2, 2, 1, 1, 1, 1, 7]
def baseStart_3148405 : Nat := 118140960795 + 3148405 * 2 ^ 59
def prefixEnd_3148405 : Nat := 4983230072969 + 3 ^ 40 * 3148405 * 2
def baseEnd_3148405 : Nat := 538881686672953194886085

theorem tailTrace_3148405 : CollatzResearch.WordTrace tailWord_3148405 prefixEnd_3148405 538881686672953194886085 := by
  unfold tailWord_3148405
  simp only [CollatzResearch.WordTrace]
  refine ⟨114831764158873864610246669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76554509439249243073497779 114831764158873864610246669)
  ·
    refine ⟨43061911559577699228842501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114831764158873864610246669 43061911559577699228842501)
    ·
      refine ⟨8074108417420818605407969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43061911559577699228842501 8074108417420818605407969)
      ·
        refine ⟨6055581313065613954055977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8074108417420818605407969 6055581313065613954055977)
        ·
          refine ⟨4541685984799210465541983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6055581313065613954055977 4541685984799210465541983)
          ·
            refine ⟨6812528977198815698312975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4541685984799210465541983 6812528977198815698312975)
            ·
              refine ⟨10218793465798223547469463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6812528977198815698312975 10218793465798223547469463)
              ·
                refine ⟨15328190198697335321204195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10218793465798223547469463 15328190198697335321204195)
                ·
                  refine ⟨22992285298046002981806293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15328190198697335321204195 22992285298046002981806293)
                  ·
                    refine ⟨538881686672953194886085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22992285298046002981806293 538881686672953194886085)
                    ·
                      rfl

theorem cell23_3148405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_3148405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148405 prefixEnd_3148405 := by exact prefixLift 3148405
  have htrace : WordTrace (prefixWord ++ tailWord_3148405) baseStart_3148405 baseEnd_3148405 := by
    simpa [prefixWord, tailWord_3148405, baseEnd_3148405] using wordTrace_append hprefix tailTrace_3148405
  have hstable : (prefixWord ++ tailWord_3148405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148405).length < 2 ^ (prefixWord ++ tailWord_3148405).sum := by decide
  have hdescent : baseEnd_3148405 < baseStart_3148405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148411 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 5]
def baseStart_3148411 : Nat := 118140960795 + 3148411 * 2 ^ 59
def prefixEnd_3148411 : Nat := 4983230072969 + 3 ^ 40 * 3148411 * 2
def baseEnd_3148411 : Nat := 1616648140902786561183227

theorem tailTrace_3148411 : CollatzResearch.WordTrace tailWord_3148411 prefixEnd_3148411 1616648140902786561183227 := by
  unfold tailWord_3148411
  simp only [CollatzResearch.WordTrace]
  refine ⟨114831982996852127634965087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76554655331234751756643391 114831982996852127634965087)
  ·
    refine ⟨172247974495278191452447631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114831982996852127634965087 172247974495278191452447631)
    ·
      refine ⟨258371961742917287178671447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172247974495278191452447631 258371961742917287178671447)
      ·
        refine ⟨387557942614375930768007171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258371961742917287178671447 387557942614375930768007171)
        ·
          refine ⟨581336913921563896152010757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387557942614375930768007171 581336913921563896152010757)
          ·
            refine ⟨109000671360293230528502017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 581336913921563896152010757 109000671360293230528502017)
            ·
              refine ⟨81750503520219922896376513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109000671360293230528502017 81750503520219922896376513)
              ·
                refine ⟨61312877640164942172282385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81750503520219922896376513 61312877640164942172282385)
                ·
                  refine ⟨45984658230123706629211789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61312877640164942172282385 45984658230123706629211789)
                  ·
                    refine ⟨17244246836296389985954421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45984658230123706629211789 17244246836296389985954421)
                    ·
                      refine ⟨1616648140902786561183227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17244246836296389985954421 1616648140902786561183227)
                      ·
                        rfl

theorem cell23_3148411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 5].length) (baseStart_3148411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148411 prefixEnd_3148411 := by exact prefixLift 3148411
  have htrace : WordTrace (prefixWord ++ tailWord_3148411) baseStart_3148411 baseEnd_3148411 := by
    simpa [prefixWord, tailWord_3148411, baseEnd_3148411] using wordTrace_append hprefix tailTrace_3148411
  have hstable : (prefixWord ++ tailWord_3148411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148411).length < 2 ^ (prefixWord ++ tailWord_3148411).sum := by decide
  have hdescent : baseEnd_3148411 < baseStart_3148411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148431 : List Nat := [1, 1, 2, 1, 1, 1, 1, 7, 8]
def baseStart_3148431 : Nat := 118140960795 + 3148431 * 2 ^ 59
def prefixEnd_3148431 : Nat := 4983230072969 + 3 ^ 40 * 3148431 * 2
def baseEnd_3148431 : Nat := 179628712279541831437015

theorem tailTrace_3148431 : CollatzResearch.WordTrace tailWord_3148431 prefixEnd_3148431 179628712279541831437015 := by
  unfold tailWord_3148431
  simp only [CollatzResearch.WordTrace]
  refine ⟨114832712456779671050693147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76555141637853114033795431 114832712456779671050693147)
  ·
    refine ⟨172249068685169506576039721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114832712456779671050693147 172249068685169506576039721)
    ·
      refine ⟨129186801513877129932029791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172249068685169506576039721 129186801513877129932029791)
      ·
        refine ⟨193780202270815694898044687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129186801513877129932029791 193780202270815694898044687)
        ·
          refine ⟨290670303406223542347067031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193780202270815694898044687 290670303406223542347067031)
          ·
            refine ⟨436005455109335313520600547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290670303406223542347067031 436005455109335313520600547)
            ·
              refine ⟨654008182664002970280900821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436005455109335313520600547 654008182664002970280900821)
              ·
                refine ⟨15328316781187569615958613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 654008182664002970280900821 15328316781187569615958613)
                ·
                  refine ⟨179628712279541831437015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15328316781187569615958613 179628712279541831437015)
                  ·
                    rfl

theorem cell23_3148431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 8].length) (baseStart_3148431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148431 prefixEnd_3148431 := by exact prefixLift 3148431
  have htrace : WordTrace (prefixWord ++ tailWord_3148431) baseStart_3148431 baseEnd_3148431 := by
    simpa [prefixWord, tailWord_3148431, baseEnd_3148431] using wordTrace_append hprefix tailTrace_3148431
  have hstable : (prefixWord ++ tailWord_3148431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148431).length < 2 ^ (prefixWord ++ tailWord_3148431).sum := by decide
  have hdescent : baseEnd_3148431 < baseStart_3148431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148462 : List Nat := [4, 1, 4, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_3148462 : Nat := 118140960795 + 3148462 * 2 ^ 59
def prefixEnd_3148462 : Nat := 4983230072969 + 3 ^ 40 * 3148462 * 2
def baseEnd_3148462 : Nat := 1616674328416165861645493

theorem tailTrace_3148462 : CollatzResearch.WordTrace tailWord_3148462 prefixEnd_3148462 1616674328416165861645493 := by
  unfold tailWord_3148462
  simp only [CollatzResearch.WordTrace]
  refine ⟨14354230389958420418133955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76555895413111575563381093 14354230389958420418133955)
  ·
    refine ⟨21531345584937630627200933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14354230389958420418133955 21531345584937630627200933)
    ·
      refine ⟨4037127297175805742600175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21531345584937630627200933 4037127297175805742600175)
      ·
        refine ⟨6055690945763708613900263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4037127297175805742600175 6055690945763708613900263)
        ·
          refine ⟨9083536418645562920850395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6055690945763708613900263 9083536418645562920850395)
          ·
            refine ⟨13625304627968344381275593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9083536418645562920850395 13625304627968344381275593)
            ·
              refine ⟨10218978470976258285956695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13625304627968344381275593 10218978470976258285956695)
              ·
                refine ⟨15328467706464387428935043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10218978470976258285956695 15328467706464387428935043)
                ·
                  refine ⟨22992701559696581143402565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15328467706464387428935043 22992701559696581143402565)
                  ·
                    refine ⟨4311131542443108964387981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22992701559696581143402565 4311131542443108964387981)
                    ·
                      refine ⟨1616674328416165861645493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4311131542443108964387981 1616674328416165861645493)
                      ·
                        rfl

theorem cell23_3148462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_3148462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148462 prefixEnd_3148462 := by exact prefixLift 3148462
  have htrace : WordTrace (prefixWord ++ tailWord_3148462) baseStart_3148462 baseEnd_3148462 := by
    simpa [prefixWord, tailWord_3148462, baseEnd_3148462] using wordTrace_append hprefix tailTrace_3148462
  have hstable : (prefixWord ++ tailWord_3148462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148462).length < 2 ^ (prefixWord ++ tailWord_3148462).sum := by decide
  have hdescent : baseEnd_3148462 < baseStart_3148462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148469 : List Nat := [1, 3, 3, 3, 1, 1, 3, 3, 1, 4]
def baseStart_3148469 : Nat := 118140960795 + 3148469 * 2 ^ 59
def prefixEnd_3148469 : Nat := 4983230072969 + 3 ^ 40 * 3148469 * 2
def baseEnd_3148469 : Nat := 538892640926915778085987

theorem tailTrace_3148469 : CollatzResearch.WordTrace tailWord_3148469 prefixEnd_3148469 538892640926915778085987 := by
  unfold tailWord_3148469
  simp only [CollatzResearch.WordTrace]
  refine ⟨114834098430642003540576461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76556065620428002360384307 114834098430642003540576461)
  ·
    refine ⟨43062786911490751327716173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114834098430642003540576461 43062786911490751327716173)
    ·
      refine ⟨16148545091809031747893565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43062786911490751327716173 16148545091809031747893565)
      ·
        refine ⟨6055704409428386905460087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16148545091809031747893565 6055704409428386905460087)
        ·
          refine ⟨9083556614142580358190131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6055704409428386905460087 9083556614142580358190131)
          ·
            refine ⟨13625334921213870537285197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9083556614142580358190131 13625334921213870537285197)
            ·
              refine ⟨5109500595455201451481949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13625334921213870537285197 5109500595455201451481949)
              ·
                refine ⟨1916062723295700544305731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5109500595455201451481949 1916062723295700544305731)
                ·
                  refine ⟨2874094084943550816458597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1916062723295700544305731 2874094084943550816458597)
                  ·
                    refine ⟨538892640926915778085987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2874094084943550816458597 538892640926915778085987)
                    ·
                      rfl

theorem cell23_3148469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_3148469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148469 prefixEnd_3148469 := by exact prefixLift 3148469
  have htrace : WordTrace (prefixWord ++ tailWord_3148469) baseStart_3148469 baseEnd_3148469 := by
    simpa [prefixWord, tailWord_3148469, baseEnd_3148469] using wordTrace_append hprefix tailTrace_3148469
  have hstable : (prefixWord ++ tailWord_3148469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148469).length < 2 ^ (prefixWord ++ tailWord_3148469).sum := by decide
  have hdescent : baseEnd_3148469 < baseStart_3148469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148525 : List Nat := [1, 5, 1, 2, 1, 1, 3, 2, 1, 6]
def baseStart_3148525 : Nat := 118140960795 + 3148525 * 2 ^ 59
def prefixEnd_3148525 : Nat := 4983230072969 + 3 ^ 40 * 3148525 * 2
def baseEnd_3148525 : Nat := 538902225899133038385901

theorem tailTrace_3148525 : CollatzResearch.WordTrace tailWord_3148525 prefixEnd_3148525 538902225899133038385901 := by
  unfold tailWord_3148525
  simp only [CollatzResearch.WordTrace]
  refine ⟨114836140918439125104615029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76557427278959416736410019 114836140918439125104615029)
  ·
    refine ⟨10765888211103667978557659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114836140918439125104615029 10765888211103667978557659)
    ·
      refine ⟨16148832316655501967836489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10765888211103667978557659 16148832316655501967836489)
      ·
        refine ⟨12111624237491626475877367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16148832316655501967836489 12111624237491626475877367)
        ·
          refine ⟨18167436356237439713816051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12111624237491626475877367 18167436356237439713816051)
          ·
            refine ⟨27251154534356159570724077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18167436356237439713816051 27251154534356159570724077)
            ·
              refine ⟨10219182950383559839021529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27251154534356159570724077 10219182950383559839021529)
              ·
                refine ⟨7664387212787669879266147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10219182950383559839021529 7664387212787669879266147)
                ·
                  refine ⟨11496580819181504818899221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7664387212787669879266147 11496580819181504818899221)
                  ·
                    refine ⟨538902225899133038385901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11496580819181504818899221 538902225899133038385901)
                    ·
                      rfl

theorem cell23_3148525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_3148525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148525 prefixEnd_3148525 := by exact prefixLift 3148525
  have htrace : WordTrace (prefixWord ++ tailWord_3148525) baseStart_3148525 baseEnd_3148525 := by
    simpa [prefixWord, tailWord_3148525, baseEnd_3148525] using wordTrace_append hprefix tailTrace_3148525
  have hstable : (prefixWord ++ tailWord_3148525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148525).length < 2 ^ (prefixWord ++ tailWord_3148525).sum := by decide
  have hdescent : baseEnd_3148525 < baseStart_3148525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148568 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 4, 7]
def baseStart_3148568 : Nat := 118140960795 + 3148568 * 2 ^ 59
def prefixEnd_3148568 : Nat := 4983230072969 + 3 ^ 40 * 3148568 * 2
def baseEnd_3148568 : Nat := 538909585788514148973335

theorem tailTrace_3148568 : CollatzResearch.WordTrace tailWord_3148568 prefixEnd_3148568 538909585788514148973335 := by
  unfold tailWord_3148568
  simp only [CollatzResearch.WordTrace]
  refine ⟨57418854628641671724215179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76558472838188895632286905 57418854628641671724215179)
  ·
    refine ⟨86128281942962507586322769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57418854628641671724215179 86128281942962507586322769)
    ·
      refine ⟨64596211457221880689742077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86128281942962507586322769 64596211457221880689742077)
      ·
        refine ⟨24223579296458205258653279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64596211457221880689742077 24223579296458205258653279)
        ·
          refine ⟨36335368944687307887979919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24223579296458205258653279 36335368944687307887979919)
          ·
            refine ⟨54503053417030961831969879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36335368944687307887979919 54503053417030961831969879)
            ·
              refine ⟨81754580125546442747954819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54503053417030961831969879 81754580125546442747954819)
              ·
                refine ⟨122631870188319664121932229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81754580125546442747954819 122631870188319664121932229)
                ·
                  refine ⟨22993475660309937022862293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122631870188319664121932229 22993475660309937022862293)
                  ·
                    refine ⟨538909585788514148973335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22993475660309937022862293 538909585788514148973335)
                    ·
                      rfl

theorem cell23_3148568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 4, 7].length) (baseStart_3148568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148568 prefixEnd_3148568 := by exact prefixLift 3148568
  have htrace : WordTrace (prefixWord ++ tailWord_3148568) baseStart_3148568 baseEnd_3148568 := by
    simpa [prefixWord, tailWord_3148568, baseEnd_3148568] using wordTrace_append hprefix tailTrace_3148568
  have hstable : (prefixWord ++ tailWord_3148568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148568).length < 2 ^ (prefixWord ++ tailWord_3148568).sum := by decide
  have hdescent : baseEnd_3148568 < baseStart_3148568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148586 : List Nat := [3, 1, 4, 3, 1, 1, 1, 3, 1, 2, 3]
def baseStart_3148586 : Nat := 118140960795 + 3148586 * 2 ^ 59
def prefixEnd_3148586 : Nat := 4983230072969 + 3 ^ 40 * 3148586 * 2
def baseEnd_3148586 : Nat := 1616738000017323376494923

theorem tailTrace_3148586 : CollatzResearch.WordTrace tailWord_3148586 prefixEnd_3148586 1616738000017323376494923 := by
  unfold tailWord_3148586
  simp only [CollatzResearch.WordTrace]
  refine ⟨28709591442804533130646403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76558910514145421681723741 28709591442804533130646403)
  ·
    refine ⟨43064387164206799695969605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28709591442804533130646403 43064387164206799695969605)
    ·
      refine ⟨8074572593288774942994301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43064387164206799695969605 8074572593288774942994301)
      ·
        refine ⟨3027964722483290603622863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8074572593288774942994301 3027964722483290603622863)
        ·
          refine ⟨4541947083724935905434295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3027964722483290603622863 4541947083724935905434295)
          ·
            refine ⟨6812920625587403858151443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4541947083724935905434295 6812920625587403858151443)
            ·
              refine ⟨10219380938381105787227165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6812920625587403858151443 10219380938381105787227165)
              ·
                refine ⟨3832267851892914670210187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10219380938381105787227165 3832267851892914670210187)
                ·
                  refine ⟨5748401777839372005315281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3832267851892914670210187 5748401777839372005315281)
                  ·
                    refine ⟨4311301333379529003986461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5748401777839372005315281 4311301333379529003986461)
                    ·
                      refine ⟨1616738000017323376494923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4311301333379529003986461 1616738000017323376494923)
                      ·
                        rfl

theorem cell23_3148586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_3148586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148586 prefixEnd_3148586 := by exact prefixLift 3148586
  have htrace : WordTrace (prefixWord ++ tailWord_3148586) baseStart_3148586 baseEnd_3148586 := by
    simpa [prefixWord, tailWord_3148586, baseEnd_3148586] using wordTrace_append hprefix tailTrace_3148586
  have hstable : (prefixWord ++ tailWord_3148586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148586).length < 2 ^ (prefixWord ++ tailWord_3148586).sum := by decide
  have hdescent : baseEnd_3148586 < baseStart_3148586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148655 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 4, 3, 3]
def baseStart_3148655 : Nat := 118140960795 + 3148655 * 2 ^ 59
def prefixEnd_3148655 : Nat := 4983230072969 + 3 ^ 40 * 3148655 * 2
def baseEnd_3148655 : Nat := 1616773430182483606532105

theorem tailTrace_3148655 : CollatzResearch.WordTrace tailWord_3148655 prefixEnd_3148655 1616773430182483606532105 := by
  unfold tailWord_3148655
  simp only [CollatzResearch.WordTrace]
  refine ⟨114840882407968157306847419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76560588271978771537898279 114840882407968157306847419)
  ·
    refine ⟨172261323611952235960271129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114840882407968157306847419 172261323611952235960271129)
    ·
      refine ⟨129195992708964176970203347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172261323611952235960271129 129195992708964176970203347)
      ·
        refine ⟨193793989063446265455305021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129195992708964176970203347 193793989063446265455305021)
        ·
          refine ⟨72672745898792349545739383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193793989063446265455305021 72672745898792349545739383)
          ·
            refine ⟨109009118848188524318609075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72672745898792349545739383 109009118848188524318609075)
            ·
              refine ⟨163513678272282786477913613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109009118848188524318609075 163513678272282786477913613)
              ·
                refine ⟨61317629352106044929217605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163513678272282786477913613 61317629352106044929217605)
                ·
                  refine ⟨11497055503519883424228301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61317629352106044929217605 11497055503519883424228301)
                  ·
                    refine ⟨4311395813819956284085613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11497055503519883424228301 4311395813819956284085613)
                    ·
                      refine ⟨1616773430182483606532105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4311395813819956284085613 1616773430182483606532105)
                      ·
                        rfl

theorem cell23_3148655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 3, 3].length) (baseStart_3148655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148655 prefixEnd_3148655 := by exact prefixLift 3148655
  have htrace : WordTrace (prefixWord ++ tailWord_3148655) baseStart_3148655 baseEnd_3148655 := by
    simpa [prefixWord, tailWord_3148655, baseEnd_3148655] using wordTrace_append hprefix tailTrace_3148655
  have hstable : (prefixWord ++ tailWord_3148655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148655).length < 2 ^ (prefixWord ++ tailWord_3148655).sum := by decide
  have hdescent : baseEnd_3148655 < baseStart_3148655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148675 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 4, 5]
def baseStart_3148675 : Nat := 118140960795 + 3148675 * 2 ^ 59
def prefixEnd_3148675 : Nat := 4983230072969 + 3 ^ 40 * 3148675 * 2
def baseEnd_3148675 : Nat := 538927899931857842760671

theorem tailTrace_3148675 : CollatzResearch.WordTrace tailWord_3148675 prefixEnd_3148675 538927899931857842760671 := by
  unfold tailWord_3148675
  simp only [CollatzResearch.WordTrace]
  refine ⟨114841611867895700722575479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76561074578597133815050319 114841611867895700722575479)
  ·
    refine ⟨172262417801843551083863219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114841611867895700722575479 172262417801843551083863219)
    ·
      refine ⟨258393626702765326625794829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172262417801843551083863219 258393626702765326625794829)
      ·
        refine ⟨96897610013536997484673061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258393626702765326625794829 96897610013536997484673061)
        ·
          refine ⟨18168301877538187028376199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96897610013536997484673061 18168301877538187028376199)
          ·
            refine ⟨27252452816307280542564299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18168301877538187028376199 27252452816307280542564299)
            ·
              refine ⟨40878679224460920813846449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27252452816307280542564299 40878679224460920813846449)
              ·
                refine ⟨30659009418345690610384837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40878679224460920813846449 30659009418345690610384837)
                ·
                  refine ⟨5748564265939816989447157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30659009418345690610384837 5748564265939816989447157)
                  ·
                    refine ⟨538927899931857842760671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5748564265939816989447157 538927899931857842760671)
                    ·
                      rfl

theorem cell23_3148675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 5].length) (baseStart_3148675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148675 prefixEnd_3148675 := by exact prefixLift 3148675
  have htrace : WordTrace (prefixWord ++ tailWord_3148675) baseStart_3148675 baseEnd_3148675 := by
    simpa [prefixWord, tailWord_3148675, baseEnd_3148675] using wordTrace_append hprefix tailTrace_3148675
  have hstable : (prefixWord ++ tailWord_3148675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148675).length < 2 ^ (prefixWord ++ tailWord_3148675).sum := by decide
  have hdescent : baseEnd_3148675 < baseStart_3148675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148729 : List Nat := [1, 2, 1, 4, 2, 3, 1, 1, 2, 4, 2]
def baseStart_3148729 : Nat := 118140960795 + 3148729 * 2 ^ 59
def prefixEnd_3148729 : Nat := 4983230072969 + 3 ^ 40 * 3148729 * 2
def baseEnd_3148729 : Nat := 1616811427750916317006765

theorem tailTrace_3148729 : CollatzResearch.WordTrace tailWord_3148729 prefixEnd_3148729 1616811427750916317006765 := by
  unfold tailWord_3148729
  simp only [CollatzResearch.WordTrace]
  refine ⟨114843581409700067945041241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76562387606466711963360827 114843581409700067945041241)
  ·
    refine ⟨86132686057275050958780931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114843581409700067945041241 86132686057275050958780931)
    ·
      refine ⟨129199029085912576438171397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86132686057275050958780931 129199029085912576438171397)
      ·
        refine ⟨24224817953608608082157137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129199029085912576438171397 24224817953608608082157137)
        ·
          refine ⟨18168613465206456061617853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24224817953608608082157137 18168613465206456061617853)
          ·
            refine ⟨6813230049452421023106695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18168613465206456061617853 6813230049452421023106695)
            ·
              refine ⟨10219845074178631534660043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6813230049452421023106695 10219845074178631534660043)
              ·
                refine ⟨15329767611267947301990065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10219845074178631534660043 15329767611267947301990065)
                ·
                  refine ⟨11497325708450960476492549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15329767611267947301990065 11497325708450960476492549)
                  ·
                    refine ⟨2155748570334555089342353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11497325708450960476492549 2155748570334555089342353)
                    ·
                      refine ⟨1616811427750916317006765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2155748570334555089342353 1616811427750916317006765)
                      ·
                        rfl

theorem cell23_3148729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_3148729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148729 prefixEnd_3148729 := by exact prefixLift 3148729
  have htrace : WordTrace (prefixWord ++ tailWord_3148729) baseStart_3148729 baseEnd_3148729 := by
    simpa [prefixWord, tailWord_3148729, baseEnd_3148729] using wordTrace_append hprefix tailTrace_3148729
  have hstable : (prefixWord ++ tailWord_3148729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148729).length < 2 ^ (prefixWord ++ tailWord_3148729).sum := by decide
  have hdescent : baseEnd_3148729 < baseStart_3148729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148756 : List Nat := [2, 4, 1, 2, 1, 2, 1, 5, 1, 4]
def baseStart_3148756 : Nat := 118140960795 + 3148756 * 2 ^ 59
def prefixEnd_3148756 : Nat := 4983230072969 + 3 ^ 40 * 3148756 * 2
def baseEnd_3148756 : Nat := 538941763909529237123047

theorem tailTrace_3148756 : CollatzResearch.WordTrace tailWord_3148756 prefixEnd_3148756 538941763909529237123047 := by
  unfold tailWord_3148756
  simp only [CollatzResearch.WordTrace]
  refine ⟨57422283090301125778137061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76563044120401501037516081 57422283090301125778137061)
  ·
    refine ⟨10766678079431461083400699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57422283090301125778137061 10766678079431461083400699)
    ·
      refine ⟨16150017119147191625101049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10766678079431461083400699 16150017119147191625101049)
      ·
        refine ⟨12112512839360393718825787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16150017119147191625101049 12112512839360393718825787)
        ·
          refine ⟨18168769259040590578238681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12112512839360393718825787 18168769259040590578238681)
          ·
            refine ⟨13626576944280442933679011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18168769259040590578238681 13626576944280442933679011)
            ·
              refine ⟨20439865416420664400518517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13626576944280442933679011 20439865416420664400518517)
              ·
                refine ⟨1916237382789437287548611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20439865416420664400518517 1916237382789437287548611)
                ·
                  refine ⟨2874356074184155931322917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1916237382789437287548611 2874356074184155931322917)
                  ·
                    refine ⟨538941763909529237123047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2874356074184155931322917 538941763909529237123047)
                    ·
                      rfl

theorem cell23_3148756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_3148756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148756 prefixEnd_3148756 := by exact prefixLift 3148756
  have htrace : WordTrace (prefixWord ++ tailWord_3148756) baseStart_3148756 baseEnd_3148756 := by
    simpa [prefixWord, tailWord_3148756, baseEnd_3148756] using wordTrace_append hprefix tailTrace_3148756
  have hstable : (prefixWord ++ tailWord_3148756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148756).length < 2 ^ (prefixWord ++ tailWord_3148756).sum := by decide
  have hdescent : baseEnd_3148756 < baseStart_3148756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148815 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 6]
def baseStart_3148815 : Nat := 118140960795 + 3148815 * 2 ^ 59
def prefixEnd_3148815 : Nat := 4983230072969 + 3 ^ 40 * 3148815 * 2
def baseEnd_3148815 : Nat := 1616855587087202980531369

theorem tailTrace_3148815 : CollatzResearch.WordTrace tailWord_3148815 prefixEnd_3148815 1616855587087202980531369 := by
  unfold tailWord_3148815
  simp only [CollatzResearch.WordTrace]
  refine ⟨114846718087388504632671899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76564478724925669755114599 114846718087388504632671899)
  ·
    refine ⟨172270077131082756949007849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114846718087388504632671899 172270077131082756949007849)
    ·
      refine ⟨129202557848312067711755887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172270077131082756949007849 129202557848312067711755887)
      ·
        refine ⟨193803836772468101567633831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129202557848312067711755887 193803836772468101567633831)
        ·
          refine ⟨290705755158702152351450747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193803836772468101567633831 290705755158702152351450747)
          ·
            refine ⟨436058632738053228527176121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290705755158702152351450747 436058632738053228527176121)
            ·
              refine ⟨327043974553539921395382091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 436058632738053228527176121 327043974553539921395382091)
              ·
                refine ⟨490565961830309882093073137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327043974553539921395382091 490565961830309882093073137)
                ·
                  refine ⟨367924471372732411569804853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 490565961830309882093073137 367924471372732411569804853)
                  ·
                    refine ⟨34492919191193663584669205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 367924471372732411569804853 34492919191193663584669205)
                    ·
                      refine ⟨1616855587087202980531369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34492919191193663584669205 1616855587087202980531369)
                      ·
                        rfl

theorem cell23_3148815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 6].length) (baseStart_3148815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148815 prefixEnd_3148815 := by exact prefixLift 3148815
  have htrace : WordTrace (prefixWord ++ tailWord_3148815) baseStart_3148815 baseEnd_3148815 := by
    simpa [prefixWord, tailWord_3148815, baseEnd_3148815] using wordTrace_append hprefix tailTrace_3148815
  have hstable : (prefixWord ++ tailWord_3148815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148815).length < 2 ^ (prefixWord ++ tailWord_3148815).sum := by decide
  have hdescent : baseEnd_3148815 < baseStart_3148815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148825 : List Nat := [1, 2, 1, 2, 1, 1, 15]
def baseStart_3148825 : Nat := 118140960795 + 3148825 * 2 ^ 59
def prefixEnd_3148825 : Nat := 4983230072969 + 3 ^ 40 * 3148825 * 2
def baseEnd_3148825 : Nat := 19961243480169727671683

theorem tailTrace_3148825 : CollatzResearch.WordTrace tailWord_3148825 prefixEnd_3148825 19961243480169727671683 := by
  unfold tailWord_3148825
  simp only [CollatzResearch.WordTrace]
  refine ⟨114847082817352276340535929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76564721878234850893690619 114847082817352276340535929)
  ·
    refine ⟨86135312113014207255401947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114847082817352276340535929 86135312113014207255401947)
    ·
      refine ⟨129202968169521310883102921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86135312113014207255401947 129202968169521310883102921)
      ·
        refine ⟨96902226127140983162327191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129202968169521310883102921 96902226127140983162327191)
        ·
          refine ⟨145353339190711474743490787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96902226127140983162327191 145353339190711474743490787)
          ·
            refine ⟨218030008786067212115236181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145353339190711474743490787 218030008786067212115236181)
            ·
              refine ⟨19961243480169727671683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 15 218030008786067212115236181 19961243480169727671683)
              ·
                rfl

theorem cell23_3148825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 15].length) (baseStart_3148825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148825 prefixEnd_3148825 := by exact prefixLift 3148825
  have htrace : WordTrace (prefixWord ++ tailWord_3148825) baseStart_3148825 baseEnd_3148825 := by
    simpa [prefixWord, tailWord_3148825, baseEnd_3148825] using wordTrace_append hprefix tailTrace_3148825
  have hstable : (prefixWord ++ tailWord_3148825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148825).length < 2 ^ (prefixWord ++ tailWord_3148825).sum := by decide
  have hdescent : baseEnd_3148825 < baseStart_3148825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148846 : List Nat := [4, 1, 3, 1, 1, 1, 3, 3, 2, 4]
def baseStart_3148846 : Nat := 118140960795 + 3148846 * 2 ^ 59
def prefixEnd_3148846 : Nat := 4983230072969 + 3 ^ 40 * 3148846 * 2
def baseEnd_3148846 : Nat := 538957168329164119747909

theorem tailTrace_3148846 : CollatzResearch.WordTrace tailWord_3148846 prefixEnd_3148846 538957168329164119747909 := by
  unfold tailWord_3148846
  simp only [CollatzResearch.WordTrace]
  refine ⟨14355981093784524615881299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76565232500184131284700261 14355981093784524615881299)
  ·
    refine ⟨21533971640676786923821949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14355981093784524615881299 21533971640676786923821949)
    ·
      refine ⟨8075239365253795096433231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21533971640676786923821949 8075239365253795096433231)
      ·
        refine ⟨12112859047880692644649847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8075239365253795096433231 12112859047880692644649847)
        ·
          refine ⟨18169288571821038966974771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12112859047880692644649847 18169288571821038966974771)
          ·
            refine ⟨27253932857731558450462157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18169288571821038966974771 27253932857731558450462157)
            ·
              refine ⟨10220224821649334418923309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27253932857731558450462157 10220224821649334418923309)
              ·
                refine ⟨3832584308118500407096241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10220224821649334418923309 3832584308118500407096241)
                ·
                  refine ⟨2874438231088875305322181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3832584308118500407096241 2874438231088875305322181)
                  ·
                    refine ⟨538957168329164119747909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2874438231088875305322181 538957168329164119747909)
                    ·
                      rfl

theorem cell23_3148846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_3148846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148846 prefixEnd_3148846 := by exact prefixLift 3148846
  have htrace : WordTrace (prefixWord ++ tailWord_3148846) baseStart_3148846 baseEnd_3148846 := by
    simpa [prefixWord, tailWord_3148846, baseEnd_3148846] using wordTrace_append hprefix tailTrace_3148846
  have hstable : (prefixWord ++ tailWord_3148846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148846).length < 2 ^ (prefixWord ++ tailWord_3148846).sum := by decide
  have hdescent : baseEnd_3148846 < baseStart_3148846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148856 : List Nat := [2, 1, 2, 1, 5, 1, 3, 2, 1, 2, 3]
def baseStart_3148856 : Nat := 118140960795 + 3148856 * 2 ^ 59
def prefixEnd_3148856 : Nat := 4983230072969 + 3 ^ 40 * 3148856 * 2
def baseEnd_3148856 : Nat := 1616876639794037320118681

theorem tailTrace_3148856 : CollatzResearch.WordTrace tailWord_3148856 prefixEnd_3148856 1616876639794037320118681 := by
  unfold tailWord_3148856
  simp only [CollatzResearch.WordTrace]
  refine ⟨57424106740119984317457211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76565475653493312423276281 57424106740119984317457211)
  ·
    refine ⟨86136160110179976476185817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57424106740119984317457211 86136160110179976476185817)
    ·
      refine ⟨64602120082634982357139363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86136160110179976476185817 64602120082634982357139363)
      ·
        refine ⟨96903180123952473535709045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64602120082634982357139363 96903180123952473535709045)
        ·
          refine ⟨9084673136620544393972723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96903180123952473535709045 9084673136620544393972723)
          ·
            refine ⟨13627009704930816590959085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9084673136620544393972723 13627009704930816590959085)
            ·
              refine ⟨5110128639349056221609657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13627009704930816590959085 5110128639349056221609657)
              ·
                refine ⟨3832596479511792166207243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5110128639349056221609657 3832596479511792166207243)
                ·
                  refine ⟨5748894719267688249310865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3832596479511792166207243 5748894719267688249310865)
                  ·
                    refine ⟨4311671039450766186983149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5748894719267688249310865 4311671039450766186983149)
                    ·
                      refine ⟨1616876639794037320118681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4311671039450766186983149 1616876639794037320118681)
                      ·
                        rfl

theorem cell23_3148856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 1, 2, 3].length) (baseStart_3148856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148856 prefixEnd_3148856 := by exact prefixLift 3148856
  have htrace : WordTrace (prefixWord ++ tailWord_3148856) baseStart_3148856 baseEnd_3148856 := by
    simpa [prefixWord, tailWord_3148856, baseEnd_3148856] using wordTrace_append hprefix tailTrace_3148856
  have hstable : (prefixWord ++ tailWord_3148856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148856).length < 2 ^ (prefixWord ++ tailWord_3148856).sum := by decide
  have hdescent : baseEnd_3148856 < baseStart_3148856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148869 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 6, 1, 3]
def baseStart_3148869 : Nat := 118140960795 + 3148869 * 2 ^ 59
def prefixEnd_3148869 : Nat := 4983230072969 + 3 ^ 40 * 3148869 * 2
def baseEnd_3148869 : Nat := 1616883315042545769256121

theorem tailTrace_3148869 : CollatzResearch.WordTrace tailWord_3148869 prefixEnd_3148869 1616883315042545769256121 := by
  unfold tailWord_3148869
  simp only [CollatzResearch.WordTrace]
  refine ⟨114848687629192871855137661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76565791752795247903425107 114848687629192871855137661)
  ·
    refine ⟨43068257860947326945676623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114848687629192871855137661 43068257860947326945676623)
    ·
      refine ⟨64602386791420990418514935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43068257860947326945676623 64602386791420990418514935)
      ·
        refine ⟨96903580187131485627772403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64602386791420990418514935 96903580187131485627772403)
        ·
          refine ⟨145355370280697228441658605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96903580187131485627772403 145355370280697228441658605)
          ·
            refine ⟨54508263855261460665621977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145355370280697228441658605 54508263855261460665621977)
            ·
              refine ⟨40881197891446095499216483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54508263855261460665621977 40881197891446095499216483)
              ·
                refine ⟨61321796837169143248824725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40881197891446095499216483 61321796837169143248824725)
                ·
                  refine ⟨2874459226742303589788659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61321796837169143248824725 2874459226742303589788659)
                  ·
                    refine ⟨4311688840113455384682989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2874459226742303589788659 4311688840113455384682989)
                    ·
                      refine ⟨1616883315042545769256121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4311688840113455384682989 1616883315042545769256121)
                      ·
                        rfl

theorem cell23_3148869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 6, 1, 3].length) (baseStart_3148869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148869 prefixEnd_3148869 := by exact prefixLift 3148869
  have htrace : WordTrace (prefixWord ++ tailWord_3148869) baseStart_3148869 baseEnd_3148869 := by
    simpa [prefixWord, tailWord_3148869, baseEnd_3148869] using wordTrace_append hprefix tailTrace_3148869
  have hstable : (prefixWord ++ tailWord_3148869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148869).length < 2 ^ (prefixWord ++ tailWord_3148869).sum := by decide
  have hdescent : baseEnd_3148869 < baseStart_3148869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148870 : List Nat := [6, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4]
def baseStart_3148870 : Nat := 118140960795 + 3148870 * 2 ^ 59
def prefixEnd_3148870 : Nat := 4983230072969 + 3 ^ 40 * 3148870 * 2
def baseEnd_3148870 : Nat := 1616883828523200265343617

theorem tailTrace_3148870 : CollatzResearch.WordTrace tailWord_3148870 prefixEnd_3148870 1616883828523200265343617 := by
  unfold tailWord_3148870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3589022628193414032060127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 76565816068126166017282709 3589022628193414032060127)
  ·
    refine ⟨5383533942290121048090191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3589022628193414032060127 5383533942290121048090191)
    ·
      refine ⟨8075300913435181572135287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5383533942290121048090191 8075300913435181572135287)
      ·
        refine ⟨12112951370152772358202931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8075300913435181572135287 12112951370152772358202931)
        ·
          refine ⟨18169427055229158537304397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12112951370152772358202931 18169427055229158537304397)
          ·
            refine ⟨6813535145710934451489149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18169427055229158537304397 6813535145710934451489149)
            ·
              refine ⟨2555075679641600419308431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6813535145710934451489149 2555075679641600419308431)
              ·
                refine ⟨3832613519462400628962647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2555075679641600419308431 3832613519462400628962647)
                ·
                  refine ⟨5748920279193600943443971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3832613519462400628962647 5748920279193600943443971)
                  ·
                    refine ⟨8623380418790401415165957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5748920279193600943443971 8623380418790401415165957)
                    ·
                      refine ⟨1616883828523200265343617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8623380418790401415165957 1616883828523200265343617)
                      ·
                        rfl

theorem cell23_3148870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_3148870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148870 prefixEnd_3148870 := by exact prefixLift 3148870
  have htrace : WordTrace (prefixWord ++ tailWord_3148870) baseStart_3148870 baseEnd_3148870 := by
    simpa [prefixWord, tailWord_3148870, baseEnd_3148870] using wordTrace_append hprefix tailTrace_3148870
  have hstable : (prefixWord ++ tailWord_3148870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148870).length < 2 ^ (prefixWord ++ tailWord_3148870).sum := by decide
  have hdescent : baseEnd_3148870 < baseStart_3148870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148879 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 7, 3, 2]
def baseStart_3148879 : Nat := 118140960795 + 3148879 * 2 ^ 59
def prefixEnd_3148879 : Nat := 4983230072969 + 3 ^ 40 * 3148879 * 2
def baseEnd_3148879 : Nat := 1616888449849090730131075

theorem tailTrace_3148879 : CollatzResearch.WordTrace tailWord_3148879 prefixEnd_3148879 1616888449849090730131075 := by
  unfold tailWord_3148879
  simp only [CollatzResearch.WordTrace]
  refine ⟨114849052359156643563001691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76566034906104429042001127 114849052359156643563001691)
  ·
    refine ⟨172273578538734965344502537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114849052359156643563001691 172273578538734965344502537)
    ·
      refine ⟨129205183904051224008376903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172273578538734965344502537 129205183904051224008376903)
      ·
        refine ⟨193807775856076836012565355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129205183904051224008376903 193807775856076836012565355)
        ·
          refine ⟨290711663784115254018848033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193807775856076836012565355 290711663784115254018848033)
          ·
            refine ⟨218033747838086440514136025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290711663784115254018848033 218033747838086440514136025)
            ·
              refine ⟨163525310878564830385602019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218033747838086440514136025 163525310878564830385602019)
              ·
                refine ⟨245287966317847245578403029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163525310878564830385602019 245287966317847245578403029)
                ·
                  refine ⟨5748936710574544818243821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 245287966317847245578403029 5748936710574544818243821)
                  ·
                    refine ⟨2155851266465454306841433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5748936710574544818243821 2155851266465454306841433)
                    ·
                      refine ⟨1616888449849090730131075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2155851266465454306841433 1616888449849090730131075)
                      ·
                        rfl

theorem cell23_3148879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 3, 2].length) (baseStart_3148879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148879 prefixEnd_3148879 := by exact prefixLift 3148879
  have htrace : WordTrace (prefixWord ++ tailWord_3148879) baseStart_3148879 baseEnd_3148879 := by
    simpa [prefixWord, tailWord_3148879, baseEnd_3148879] using wordTrace_append hprefix tailTrace_3148879
  have hstable : (prefixWord ++ tailWord_3148879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148879).length < 2 ^ (prefixWord ++ tailWord_3148879).sum := by decide
  have hdescent : baseEnd_3148879 < baseStart_3148879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148893 : List Nat := [1, 4, 4, 1, 3, 1, 1, 8]
def baseStart_3148893 : Nat := 118140960795 + 3148893 * 2 ^ 59
def prefixEnd_3148893 : Nat := 4983230072969 + 3 ^ 40 * 3148893 * 2
def baseEnd_3148893 : Nat := 59885023651046432420593

theorem tailTrace_3148893 : CollatzResearch.WordTrace tailWord_3148893 prefixEnd_3148893 59885023651046432420593 := by
  unfold tailWord_3148893
  simp only [CollatzResearch.WordTrace]
  refine ⟨114849562981105923954011333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76566375320737282636007555 114849562981105923954011333)
  ·
    refine ⟨21534293058957360741377125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114849562981105923954011333 21534293058957360741377125)
    ·
      refine ⟨4037679948554505139008211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21534293058957360741377125 4037679948554505139008211)
      ·
        refine ⟨6056519922831757708512317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4037679948554505139008211 6056519922831757708512317)
        ·
          refine ⟨2271194971061909140692119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6056519922831757708512317 2271194971061909140692119)
          ·
            refine ⟨3406792456592863711038179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2271194971061909140692119 3406792456592863711038179)
            ·
              refine ⟨5110188684889295566557269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3406792456592863711038179 5110188684889295566557269)
              ·
                refine ⟨59885023651046432420593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5110188684889295566557269 59885023651046432420593)
                ·
                  rfl

theorem cell23_3148893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 8].length) (baseStart_3148893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148893 prefixEnd_3148893 := by exact prefixLift 3148893
  have htrace : WordTrace (prefixWord ++ tailWord_3148893) baseStart_3148893 baseEnd_3148893 := by
    simpa [prefixWord, tailWord_3148893, baseEnd_3148893] using wordTrace_append hprefix tailTrace_3148893
  have hstable : (prefixWord ++ tailWord_3148893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148893).length < 2 ^ (prefixWord ++ tailWord_3148893).sum := by decide
  have hdescent : baseEnd_3148893 < baseStart_3148893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148960 : List Nat := [2, 1, 1, 4, 2, 1, 5, 1, 2, 2, 2]
def baseStart_3148960 : Nat := 118140960795 + 3148960 * 2 ^ 59
def prefixEnd_3148960 : Nat := 4983230072969 + 3 ^ 40 * 3148960 * 2
def baseEnd_3148960 : Nat := 1616930041782104913218203

theorem tailTrace_3148960 : CollatzResearch.WordTrace tailWord_3148960 prefixEnd_3148960 1616930041782104913218203 := by
  unfold tailWord_3148960
  simp only [CollatzResearch.WordTrace]
  refine ⟨57426003335931597198350167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76568004447908796264466889 57426003335931597198350167)
  ·
    refine ⟨86139005003897395797525251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57426003335931597198350167 86139005003897395797525251)
    ·
      refine ⟨129208507505846093696287877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86139005003897395797525251 129208507505846093696287877)
      ·
        refine ⟨24226595157346142568053977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129208507505846093696287877 24226595157346142568053977)
        ·
          refine ⟨18169946368009606926040483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24226595157346142568053977 18169946368009606926040483)
          ·
            refine ⟨27254919552014410389060725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18169946368009606926040483 27254919552014410389060725)
            ·
              refine ⟨2555148708001350973974443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27254919552014410389060725 2555148708001350973974443)
              ·
                refine ⟨3832723062002026460961665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2555148708001350973974443 3832723062002026460961665)
                ·
                  refine ⟨2874542296501519845721249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3832723062002026460961665 2874542296501519845721249)
                  ·
                    refine ⟨2155906722376139884290937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2874542296501519845721249 2155906722376139884290937)
                    ·
                      refine ⟨1616930041782104913218203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2155906722376139884290937 1616930041782104913218203)
                      ·
                        rfl

theorem cell23_3148960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_3148960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148960 prefixEnd_3148960 := by exact prefixLift 3148960
  have htrace : WordTrace (prefixWord ++ tailWord_3148960) baseStart_3148960 baseEnd_3148960 := by
    simpa [prefixWord, tailWord_3148960, baseEnd_3148960] using wordTrace_append hprefix tailTrace_3148960
  have hstable : (prefixWord ++ tailWord_3148960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148960).length < 2 ^ (prefixWord ++ tailWord_3148960).sum := by decide
  have hdescent : baseEnd_3148960 < baseStart_3148960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3148972 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 7]
def baseStart_3148972 : Nat := 118140960795 + 3148972 * 2 ^ 59
def prefixEnd_3148972 : Nat := 4983230072969 + 3 ^ 40 * 3148972 * 2
def baseEnd_3148972 : Nat := 1616936203549958866268147

theorem tailTrace_3148972 : CollatzResearch.WordTrace tailWord_3148972 prefixEnd_3148972 1616936203549958866268147 := by
  unfold tailWord_3148972
  simp only [CollatzResearch.WordTrace]
  refine ⟨57426222173909860223068585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76568296231879813630758113 57426222173909860223068585)
  ·
    refine ⟨43069666630432395167301439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57426222173909860223068585 43069666630432395167301439)
    ·
      refine ⟨64604499945648592750952159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43069666630432395167301439 64604499945648592750952159)
      ·
        refine ⟨96906749918472889126428239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64604499945648592750952159 96906749918472889126428239)
        ·
          refine ⟨145360124877709333689642359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96906749918472889126428239 145360124877709333689642359)
          ·
            refine ⟨218040187316564000534463539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145360124877709333689642359 218040187316564000534463539)
            ·
              refine ⟨327060280974846000801695309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218040187316564000534463539 327060280974846000801695309)
              ·
                refine ⟨122647605365567250300635741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 327060280974846000801695309 122647605365567250300635741)
                ·
                  refine ⟨45992852012087718862738403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122647605365567250300635741 45992852012087718862738403)
                  ·
                    refine ⟨68989278018131578294107605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45992852012087718862738403 68989278018131578294107605)
                    ·
                      refine ⟨1616936203549958866268147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68989278018131578294107605 1616936203549958866268147)
                      ·
                        rfl

theorem cell23_3148972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_3148972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3148972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3148972 prefixEnd_3148972 := by exact prefixLift 3148972
  have htrace : WordTrace (prefixWord ++ tailWord_3148972) baseStart_3148972 baseEnd_3148972 := by
    simpa [prefixWord, tailWord_3148972, baseEnd_3148972] using wordTrace_append hprefix tailTrace_3148972
  have hstable : (prefixWord ++ tailWord_3148972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3148972).length < 2 ^ (prefixWord ++ tailWord_3148972).sum := by decide
  have hdescent : baseEnd_3148972 < baseStart_3148972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3148972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149006 : List Nat := [4, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5]
def baseStart_3149006 : Nat := 118140960795 + 3149006 * 2 ^ 59
def prefixEnd_3149006 : Nat := 4983230072969 + 3 ^ 40 * 3149006 * 2
def baseEnd_3149006 : Nat := 1616953661892211733242991

theorem tailTrace_3149006 : CollatzResearch.WordTrace tailWord_3149006 prefixEnd_3149006 1616953661892211733242991 := by
  unfold tailWord_3149006
  simp only [CollatzResearch.WordTrace]
  refine ⟨14356710553712068031609359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76569122953131029501916581 14356710553712068031609359)
  ·
    refine ⟨21535065830568102047414039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14356710553712068031609359 21535065830568102047414039)
    ·
      refine ⟨32302598745852153071121059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21535065830568102047414039 32302598745852153071121059)
      ·
        refine ⟨48453898118778229606681589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32302598745852153071121059 48453898118778229606681589)
        ·
          refine ⟨4542552948635459025626399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48453898118778229606681589 4542552948635459025626399)
          ·
            refine ⟨6813829422953188538439599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4542552948635459025626399 6813829422953188538439599)
            ·
              refine ⟨10220744134429782807659399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6813829422953188538439599 10220744134429782807659399)
              ·
                refine ⟨15331116201644674211489099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10220744134429782807659399 15331116201644674211489099)
                ·
                  refine ⟨22996674302467011317233649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15331116201644674211489099 22996674302467011317233649)
                  ·
                    refine ⟨17247505726850258487925237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22996674302467011317233649 17247505726850258487925237)
                    ·
                      refine ⟨1616953661892211733242991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17247505726850258487925237 1616953661892211733242991)
                      ·
                        rfl

theorem cell23_3149006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_3149006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149006 prefixEnd_3149006 := by exact prefixLift 3149006
  have htrace : WordTrace (prefixWord ++ tailWord_3149006) baseStart_3149006 baseEnd_3149006 := by
    simpa [prefixWord, tailWord_3149006, baseEnd_3149006] using wordTrace_append hprefix tailTrace_3149006
  have hstable : (prefixWord ++ tailWord_3149006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149006).length < 2 ^ (prefixWord ++ tailWord_3149006).sum := by decide
  have hdescent : baseEnd_3149006 < baseStart_3149006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149036 : List Nat := [2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 3]
def baseStart_3149036 : Nat := 118140960795 + 3149036 * 2 ^ 59
def prefixEnd_3149036 : Nat := 4983230072969 + 3 ^ 40 * 3149036 * 2
def baseEnd_3149036 : Nat := 1616969066311846615867853

theorem tailTrace_3149036 : CollatzResearch.WordTrace tailWord_3149036 prefixEnd_3149036 1616969066311846615867853 := by
  unfold tailWord_3149036
  simp only [CollatzResearch.WordTrace]
  refine ⟨57427389309793929688233481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76569852413058572917644641 57427389309793929688233481)
  ·
    refine ⟨43070541982345447266175111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57427389309793929688233481 43070541982345447266175111)
    ·
      refine ⟨64605812973518170899262667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43070541982345447266175111 64605812973518170899262667)
      ·
        refine ⟨96908719460277256348894001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64605812973518170899262667 96908719460277256348894001)
        ·
          refine ⟨72681539595207942261670501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96908719460277256348894001 72681539595207942261670501)
          ·
            refine ⟨13627788674101489174063219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72681539595207942261670501 13627788674101489174063219)
            ·
              refine ⟨20441683011152233761094829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13627788674101489174063219 20441683011152233761094829)
              ·
                refine ⟨7665631129182087660410561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20441683011152233761094829 7665631129182087660410561)
                ·
                  refine ⟨5749223346886565745307921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7665631129182087660410561 5749223346886565745307921)
                  ·
                    refine ⟨4311917510164924308980941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5749223346886565745307921 4311917510164924308980941)
                    ·
                      refine ⟨1616969066311846615867853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4311917510164924308980941 1616969066311846615867853)
                      ·
                        rfl

theorem cell23_3149036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 3].length) (baseStart_3149036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149036 prefixEnd_3149036 := by exact prefixLift 3149036
  have htrace : WordTrace (prefixWord ++ tailWord_3149036) baseStart_3149036 baseEnd_3149036 := by
    simpa [prefixWord, tailWord_3149036, baseEnd_3149036] using wordTrace_append hprefix tailTrace_3149036
  have hstable : (prefixWord ++ tailWord_3149036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149036).length < 2 ^ (prefixWord ++ tailWord_3149036).sum := by decide
  have hdescent : baseEnd_3149036 < baseStart_3149036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149060 : List Nat := [2, 3, 2, 2, 2, 2, 1, 4, 1, 4]
def baseStart_3149060 : Nat := 118140960795 + 3149060 * 2 ^ 59
def prefixEnd_3149060 : Nat := 4983230072969 + 3 ^ 40 * 3149060 * 2
def baseEnd_3149060 : Nat := 538993796615851507322581

theorem tailTrace_3149060 : CollatzResearch.WordTrace tailWord_3149060 prefixEnd_3149060 538993796615851507322581 := by
  unfold tailWord_3149060
  simp only [CollatzResearch.WordTrace]
  refine ⟨57427826985750455737670317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76570435981000607650227089 57427826985750455737670317)
  ·
    refine ⟨21535435119656420901626369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57427826985750455737670317 21535435119656420901626369)
    ·
      refine ⟨16151576339742315676219777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21535435119656420901626369 16151576339742315676219777)
      ·
        refine ⟨12113682254806736757164833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16151576339742315676219777 12113682254806736757164833)
        ·
          refine ⟨9085261691105052567873625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12113682254806736757164833 9085261691105052567873625)
          ·
            refine ⟨6813946268328789425905219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9085261691105052567873625 6813946268328789425905219)
            ·
              refine ⟨10220919402493184138857829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6813946268328789425905219 10220919402493184138857829)
              ·
                refine ⟨1916422387967472026035843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10220919402493184138857829 1916422387967472026035843)
                ·
                  refine ⟨2874633581951208039053765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1916422387967472026035843 2874633581951208039053765)
                  ·
                    refine ⟨538993796615851507322581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2874633581951208039053765 538993796615851507322581)
                    ·
                      rfl

theorem cell23_3149060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_3149060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149060 prefixEnd_3149060 := by exact prefixLift 3149060
  have htrace : WordTrace (prefixWord ++ tailWord_3149060) baseStart_3149060 baseEnd_3149060 := by
    simpa [prefixWord, tailWord_3149060, baseEnd_3149060] using wordTrace_append hprefix tailTrace_3149060
  have hstable : (prefixWord ++ tailWord_3149060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149060).length < 2 ^ (prefixWord ++ tailWord_3149060).sum := by decide
  have hdescent : baseEnd_3149060 < baseStart_3149060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149079 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 7]
def baseStart_3149079 : Nat := 118140960795 + 3149079 * 2 ^ 59
def prefixEnd_3149079 : Nat := 4983230072969 + 3 ^ 40 * 3149079 * 2
def baseEnd_3149079 : Nat := 1616991145979989947630155

theorem tailTrace_3149079 : CollatzResearch.WordTrace tailWord_3149079 prefixEnd_3149079 1616991145979989947630155 := by
  unfold tailWord_3149079
  simp only [CollatzResearch.WordTrace]
  refine ⟨114856346958432077720282291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76570897972288051813521527 114856346958432077720282291)
  ·
    refine ⟨172284520437648116580423437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114856346958432077720282291 172284520437648116580423437)
    ·
      refine ⟨64606695164118043717658789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172284520437648116580423437 64606695164118043717658789)
      ·
        refine ⟨12113755343272133197061023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64606695164118043717658789 12113755343272133197061023)
        ·
          refine ⟨18170633014908199795591535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12113755343272133197061023 18170633014908199795591535)
          ·
            refine ⟨27255949522362299693387303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18170633014908199795591535 27255949522362299693387303)
            ·
              refine ⟨40883924283543449540080955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27255949522362299693387303 40883924283543449540080955)
              ·
                refine ⟨61325886425315174310121433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40883924283543449540080955 61325886425315174310121433)
                ·
                  refine ⟨45994414818986380732591075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61325886425315174310121433 45994414818986380732591075)
                  ·
                    refine ⟨68991622228479571098886613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45994414818986380732591075 68991622228479571098886613)
                    ·
                      refine ⟨1616991145979989947630155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68991622228479571098886613 1616991145979989947630155)
                      ·
                        rfl

theorem cell23_3149079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_3149079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149079 prefixEnd_3149079 := by exact prefixLift 3149079
  have htrace : WordTrace (prefixWord ++ tailWord_3149079) baseStart_3149079 baseEnd_3149079 := by
    simpa [prefixWord, tailWord_3149079, baseEnd_3149079] using wordTrace_append hprefix tailTrace_3149079
  have hstable : (prefixWord ++ tailWord_3149079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149079).length < 2 ^ (prefixWord ++ tailWord_3149079).sum := by decide
  have hdescent : baseEnd_3149079 < baseStart_3149079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149093 : List Nat := [1, 3, 1, 2, 4, 2, 1, 1, 1, 5, 2]
def baseStart_3149093 : Nat := 118140960795 + 3149093 * 2 ^ 59
def prefixEnd_3149093 : Nat := 4983230072969 + 3 ^ 40 * 3149093 * 2
def baseEnd_3149093 : Nat := 1616998334709152892855091

theorem tailTrace_3149093 : CollatzResearch.WordTrace tailWord_3149093 prefixEnd_3149093 1616998334709152892855091 := by
  unfold tailWord_3149093
  simp only [CollatzResearch.WordTrace]
  refine ⟨114856857580381358111291933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76571238386920905407527955 114856857580381358111291933)
  ·
    refine ⟨43071321592643009291734475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114856857580381358111291933 43071321592643009291734475)
    ·
      refine ⟨64606982388964513937601713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43071321592643009291734475 64606982388964513937601713)
      ·
        refine ⟨48455236791723385453201285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64606982388964513937601713 48455236791723385453201285)
        ·
          refine ⟨9085356898448134772475241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48455236791723385453201285 9085356898448134772475241)
          ·
            refine ⟨6814017673836101079356431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9085356898448134772475241 6814017673836101079356431)
            ·
              refine ⟨10221026510754151619034647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6814017673836101079356431 10221026510754151619034647)
              ·
                refine ⟨15331539766131227428551971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10221026510754151619034647 15331539766131227428551971)
                ·
                  refine ⟨22997309649196841142827957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15331539766131227428551971 22997309649196841142827957)
                  ·
                    refine ⟨2155997779612203857140121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22997309649196841142827957 2155997779612203857140121)
                    ·
                      refine ⟨1616998334709152892855091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2155997779612203857140121 1616998334709152892855091)
                      ·
                        rfl

theorem cell23_3149093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 5, 2].length) (baseStart_3149093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149093 prefixEnd_3149093 := by exact prefixLift 3149093
  have htrace : WordTrace (prefixWord ++ tailWord_3149093) baseStart_3149093 baseEnd_3149093 := by
    simpa [prefixWord, tailWord_3149093, baseEnd_3149093] using wordTrace_append hprefix tailTrace_3149093
  have hstable : (prefixWord ++ tailWord_3149093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149093).length < 2 ^ (prefixWord ++ tailWord_3149093).sum := by decide
  have hdescent : baseEnd_3149093 < baseStart_3149093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149117 : List Nat := [1, 4, 1, 5, 1, 1, 2, 1, 3, 1, 3]
def baseStart_3149117 : Nat := 118140960795 + 3149117 * 2 ^ 59
def prefixEnd_3149117 : Nat := 4983230072969 + 3 ^ 40 * 3149117 * 2
def baseEnd_3149117 : Nat := 1617010658244860798954981

theorem tailTrace_3149117 : CollatzResearch.WordTrace tailWord_3149117 prefixEnd_3149117 1617010658244860798954981 := by
  unfold tailWord_3149117
  simp only [CollatzResearch.WordTrace]
  refine ⟨114857732932294410210165605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76571821954862940140110403 114857732932294410210165605)
  ·
    refine ⟨21535824924805201914406051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114857732932294410210165605 21535824924805201914406051)
    ·
      refine ⟨32303737387207802871609077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21535824924805201914406051 32303737387207802871609077)
      ·
        refine ⟨3028475380050731519213351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32303737387207802871609077 3028475380050731519213351)
        ·
          refine ⟨4542713070076097278820027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3028475380050731519213351 4542713070076097278820027)
          ·
            refine ⟨6814069605114145918230041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4542713070076097278820027 6814069605114145918230041)
            ·
              refine ⟨5110552203835609438672531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6814069605114145918230041 5110552203835609438672531)
              ·
                refine ⟨7665828305753414158008797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5110552203835609438672531 7665828305753414158008797)
                ·
                  refine ⟨2874685614657530309253299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7665828305753414158008797 2874685614657530309253299)
                  ·
                    refine ⟨4312028421986295463879949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2874685614657530309253299 4312028421986295463879949)
                    ·
                      refine ⟨1617010658244860798954981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4312028421986295463879949 1617010658244860798954981)
                      ·
                        rfl

theorem cell23_3149117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_3149117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149117 prefixEnd_3149117 := by exact prefixLift 3149117
  have htrace : WordTrace (prefixWord ++ tailWord_3149117) baseStart_3149117 baseEnd_3149117 := by
    simpa [prefixWord, tailWord_3149117, baseEnd_3149117] using wordTrace_append hprefix tailTrace_3149117
  have hstable : (prefixWord ++ tailWord_3149117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149117).length < 2 ^ (prefixWord ++ tailWord_3149117).sum := by decide
  have hdescent : baseEnd_3149117 < baseStart_3149117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149140 : List Nat := [2, 4, 1, 1, 2, 1, 1, 4, 3, 2, 2]
def baseStart_3149140 : Nat := 118140960795 + 3149140 * 2 ^ 59
def prefixEnd_3149140 : Nat := 4983230072969 + 3 ^ 40 * 3149140 * 2
def baseEnd_3149140 : Nat := 1617022468299914208967375

theorem tailTrace_3149140 : CollatzResearch.WordTrace tailWord_3149140 prefixEnd_3149140 1617022468299914208967375 := by
  unfold tailWord_3149140
  simp only [CollatzResearch.WordTrace]
  refine ⟨57429285905605542569126437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76572381207474056758835249 57429285905605542569126437)
  ·
    refine ⟨10767991107301039231711207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57429285905605542569126437 10767991107301039231711207)
    ·
      refine ⟨16151986660951558847566811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10767991107301039231711207 16151986660951558847566811)
      ·
        refine ⟨24227979991427338271350217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16151986660951558847566811 24227979991427338271350217)
        ·
          refine ⟨18170984993570503703512663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24227979991427338271350217 18170984993570503703512663)
          ·
            refine ⟨27256477490355755555268995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18170984993570503703512663 27256477490355755555268995)
            ·
              refine ⟨40884716235533633332903493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27256477490355755555268995 40884716235533633332903493)
              ·
                refine ⟨7665884294162556249919405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40884716235533633332903493 7665884294162556249919405)
                ·
                  refine ⟨2874706610310958593719777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7665884294162556249919405 2874706610310958593719777)
                  ·
                    refine ⟨2156029957733218945289833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2874706610310958593719777 2156029957733218945289833)
                    ·
                      refine ⟨1617022468299914208967375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2156029957733218945289833 1617022468299914208967375)
                      ·
                        rfl

theorem cell23_3149140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_3149140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149140 prefixEnd_3149140 := by exact prefixLift 3149140
  have htrace : WordTrace (prefixWord ++ tailWord_3149140) baseStart_3149140 baseEnd_3149140 := by
    simpa [prefixWord, tailWord_3149140, baseEnd_3149140] using wordTrace_append hprefix tailTrace_3149140
  have hstable : (prefixWord ++ tailWord_3149140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149140).length < 2 ^ (prefixWord ++ tailWord_3149140).sum := by decide
  have hdescent : baseEnd_3149140 < baseStart_3149140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149143 : List Nat := [1, 1, 3, 2, 3, 2, 1, 4, 1, 2, 3]
def baseStart_3149143 : Nat := 118140960795 + 3149143 * 2 ^ 59
def prefixEnd_3149143 : Nat := 4983230072969 + 3 ^ 40 * 3149143 * 2
def baseEnd_3149143 : Nat := 1617024008741877697229861

theorem tailTrace_3149143 : CollatzResearch.WordTrace tailWord_3149143 prefixEnd_3149143 1617024008741877697229861 := by
  unfold tailWord_3149143
  simp only [CollatzResearch.WordTrace]
  refine ⟨114858681230200216650612083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76572454153466811100408055 114858681230200216650612083)
  ·
    refine ⟨172288021845300324975918125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114858681230200216650612083 172288021845300324975918125)
    ·
      refine ⟨64608008191987621865969297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172288021845300324975918125 64608008191987621865969297)
      ·
        refine ⟨48456006143990716399476973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64608008191987621865969297 48456006143990716399476973)
        ·
          refine ⟨18171002303996518649803865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48456006143990716399476973 18171002303996518649803865)
          ·
            refine ⟨13628251727997388987352899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18171002303996518649803865 13628251727997388987352899)
            ·
              refine ⟨20442377591996083481029349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13628251727997388987352899 20442377591996083481029349)
              ·
                refine ⟨3832945798499265652693003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20442377591996083481029349 3832945798499265652693003)
                ·
                  refine ⟨5749418697748898479039505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3832945798499265652693003 5749418697748898479039505)
                  ·
                    refine ⟨4312064023311673859279629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5749418697748898479039505 4312064023311673859279629)
                    ·
                      refine ⟨1617024008741877697229861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4312064023311673859279629 1617024008741877697229861)
                      ·
                        rfl

theorem cell23_3149143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_3149143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149143 prefixEnd_3149143 := by exact prefixLift 3149143
  have htrace : WordTrace (prefixWord ++ tailWord_3149143) baseStart_3149143 baseEnd_3149143 := by
    simpa [prefixWord, tailWord_3149143, baseEnd_3149143] using wordTrace_append hprefix tailTrace_3149143
  have hstable : (prefixWord ++ tailWord_3149143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149143).length < 2 ^ (prefixWord ++ tailWord_3149143).sum := by decide
  have hdescent : baseEnd_3149143 < baseStart_3149143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149146 : List Nat := [3, 1, 1, 2, 1, 2, 6, 7]
def baseStart_3149146 : Nat := 118140960795 + 3149146 * 2 ^ 59
def prefixEnd_3149146 : Nat := 4983230072969 + 3 ^ 40 * 3149146 * 2
def baseEnd_3149146 : Nat := 59889835154957080944161

theorem tailTrace_3149146 : CollatzResearch.WordTrace tailWord_3149146 prefixEnd_3149146 59889835154957080944161 := by
  unfold tailWord_3149146
  simp only [CollatzResearch.WordTrace]
  refine ⟨28714697662297337040742823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76572527099459565441980861 28714697662297337040742823)
  ·
    refine ⟨43072046493446005561114235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28714697662297337040742823 43072046493446005561114235)
    ·
      refine ⟨64608069740169008341671353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43072046493446005561114235 64608069740169008341671353)
      ·
        refine ⟨48456052305126756256253515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64608069740169008341671353 48456052305126756256253515)
        ·
          refine ⟨72684078457690134384380273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48456052305126756256253515 72684078457690134384380273)
          ·
            refine ⟨54513058843267600788285205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72684078457690134384380273 54513058843267600788285205)
            ·
              refine ⟨2555299633278168786950869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54513058843267600788285205 2555299633278168786950869)
              ·
                refine ⟨59889835154957080944161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2555299633278168786950869 59889835154957080944161)
                ·
                  rfl

theorem cell23_3149146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 7].length) (baseStart_3149146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149146 prefixEnd_3149146 := by exact prefixLift 3149146
  have htrace : WordTrace (prefixWord ++ tailWord_3149146) baseStart_3149146 baseEnd_3149146 := by
    simpa [prefixWord, tailWord_3149146, baseEnd_3149146] using wordTrace_append hprefix tailTrace_3149146
  have hstable : (prefixWord ++ tailWord_3149146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149146).length < 2 ^ (prefixWord ++ tailWord_3149146).sum := by decide
  have hdescent : baseEnd_3149146 < baseStart_3149146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149199 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 9]
def baseStart_3149199 : Nat := 118140960795 + 3149199 * 2 ^ 59
def prefixEnd_3149199 : Nat := 4983230072969 + 3 ^ 40 * 3149199 * 2
def baseEnd_3149199 : Nat := 1617052763658529478129603

theorem tailTrace_3149199 : CollatzResearch.WordTrace tailWord_3149199 prefixEnd_3149199 1617052763658529478129603 := by
  unfold tailWord_3149199
  simp only [CollatzResearch.WordTrace]
  refine ⟨114860723717997338214650651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76573815811998225476433767 114860723717997338214650651)
  ·
    refine ⟨172291085576996007321975977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114860723717997338214650651 172291085576996007321975977)
    ·
      refine ⟨129218314182747005491481983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172291085576996007321975977 129218314182747005491481983)
      ·
        refine ⟨193827471274120508237222975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129218314182747005491481983 193827471274120508237222975)
        ·
          refine ⟨290741206911180762355834463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193827471274120508237222975 290741206911180762355834463)
          ·
            refine ⟨436111810366771143533751695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290741206911180762355834463 436111810366771143533751695)
            ·
              refine ⟨654167715550156715300627543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436111810366771143533751695 654167715550156715300627543)
              ·
                refine ⟨981251573325235072950941315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654167715550156715300627543 981251573325235072950941315)
                ·
                  refine ⟨1471877359987852609426411973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 981251573325235072950941315 1471877359987852609426411973)
                  ·
                    refine ⟨275977004997722364267452245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1471877359987852609426411973 275977004997722364267452245)
                    ·
                      refine ⟨1617052763658529478129603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 275977004997722364267452245 1617052763658529478129603)
                      ·
                        rfl

theorem cell23_3149199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 9].length) (baseStart_3149199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149199 prefixEnd_3149199 := by exact prefixLift 3149199
  have htrace : WordTrace (prefixWord ++ tailWord_3149199) baseStart_3149199 baseEnd_3149199 := by
    simpa [prefixWord, tailWord_3149199, baseEnd_3149199] using wordTrace_append hprefix tailTrace_3149199
  have hstable : (prefixWord ++ tailWord_3149199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149199).length < 2 ^ (prefixWord ++ tailWord_3149199).sum := by decide
  have hdescent : baseEnd_3149199 < baseStart_3149199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149216 : List Nat := [2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 5]
def baseStart_3149216 : Nat := 118140960795 + 3149216 * 2 ^ 59
def prefixEnd_3149216 : Nat := 4983230072969 + 3 ^ 40 * 3149216 * 2
def baseEnd_3149216 : Nat := 1617061492829655911617025

theorem tailTrace_3149216 : CollatzResearch.WordTrace tailWord_3149216 prefixEnd_3149216 1617061492829655911617025 := by
  unfold tailWord_3149216
  simp only [CollatzResearch.WordTrace]
  refine ⟨57430671879467875059009751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76574229172623833412013001 57430671879467875059009751)
  ·
    refine ⟨86146007819201812588514627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57430671879467875059009751 86146007819201812588514627)
    ·
      refine ⟨129219011728802718882771941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86146007819201812588514627 129219011728802718882771941)
      ·
        refine ⟨24228564699150509790519739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129219011728802718882771941 24228564699150509790519739)
        ·
          refine ⟨36342847048725764685779609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24228564699150509790519739 36342847048725764685779609)
          ·
            refine ⟨27257135286544323514334707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36342847048725764685779609 27257135286544323514334707)
            ·
              refine ⟨40885702929816485271502061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27257135286544323514334707 40885702929816485271502061)
              ·
                refine ⟨15332138598681181976813273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40885702929816485271502061 15332138598681181976813273)
                ·
                  refine ⟨11499103949010886482609955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15332138598681181976813273 11499103949010886482609955)
                  ·
                    refine ⟨17248655923516329723914933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11499103949010886482609955 17248655923516329723914933)
                    ·
                      refine ⟨1617061492829655911617025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17248655923516329723914933 1617061492829655911617025)
                      ·
                        rfl

theorem cell23_3149216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_3149216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149216 prefixEnd_3149216 := by exact prefixLift 3149216
  have htrace : WordTrace (prefixWord ++ tailWord_3149216) baseStart_3149216 baseEnd_3149216 := by
    simpa [prefixWord, tailWord_3149216, baseEnd_3149216] using wordTrace_append hprefix tailTrace_3149216
  have hstable : (prefixWord ++ tailWord_3149216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149216).length < 2 ^ (prefixWord ++ tailWord_3149216).sum := by decide
  have hdescent : baseEnd_3149216 < baseStart_3149216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149224 : List Nat := [2, 1, 6, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_3149224 : Nat := 118140960795 + 3149224 * 2 ^ 59
def prefixEnd_3149224 : Nat := 4983230072969 + 3 ^ 40 * 3149224 * 2
def baseEnd_3149224 : Nat := 1617065600674891880316989

theorem tailTrace_3149224 : CollatzResearch.WordTrace tailWord_3149224 prefixEnd_3149224 1617065600674891880316989 := by
  unfold tailWord_3149224
  simp only [CollatzResearch.WordTrace]
  refine ⟨57430817771453383742155363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76574423695271178322873817 57430817771453383742155363)
  ·
    refine ⟨86146226657180075613233045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57430817771453383742155363 86146226657180075613233045)
    ·
      refine ⟨4038104374555316044370299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86146226657180075613233045 4038104374555316044370299)
      ·
        refine ⟨6057156561832974066555449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4038104374555316044370299 6057156561832974066555449)
        ·
          refine ⟨4542867421374730549916587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6057156561832974066555449 4542867421374730549916587)
          ·
            refine ⟨6814301132062095824874881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4542867421374730549916587 6814301132062095824874881)
            ·
              refine ⟨5110725849046571868656161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6814301132062095824874881 5110725849046571868656161)
              ·
                refine ⟨3833044386784928901492121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5110725849046571868656161 3833044386784928901492121)
                ·
                  refine ⟨2874783290088696676119091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3833044386784928901492121 2874783290088696676119091)
                  ·
                    refine ⟨4312174935133045014178637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2874783290088696676119091 4312174935133045014178637)
                    ·
                      refine ⟨1617065600674891880316989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4312174935133045014178637 1617065600674891880316989)
                      ·
                        rfl

theorem cell23_3149224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_3149224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149224 prefixEnd_3149224 := by exact prefixLift 3149224
  have htrace : WordTrace (prefixWord ++ tailWord_3149224) baseStart_3149224 baseEnd_3149224 := by
    simpa [prefixWord, tailWord_3149224, baseEnd_3149224] using wordTrace_append hprefix tailTrace_3149224
  have hstable : (prefixWord ++ tailWord_3149224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149224).length < 2 ^ (prefixWord ++ tailWord_3149224).sum := by decide
  have hdescent : baseEnd_3149224 < baseStart_3149224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149303 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 1, 6, 2]
def baseStart_3149303 : Nat := 118140960795 + 3149303 * 2 ^ 59
def prefixEnd_3149303 : Nat := 4983230072969 + 3 ^ 40 * 3149303 * 2
def baseEnd_3149303 : Nat := 1617106165646597071229125

theorem tailTrace_3149303 : CollatzResearch.WordTrace tailWord_3149303 prefixEnd_3149303 1617106165646597071229125 := by
  unfold tailWord_3149303
  simp only [CollatzResearch.WordTrace]
  refine ⟨114864516909620563976436563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76576344606413709317624375 114864516909620563976436563)
  ·
    refine ⟨172296775364430845964654845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114864516909620563976436563 172296775364430845964654845)
    ·
      refine ⟨64611290761661567236745567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172296775364430845964654845 64611290761661567236745567)
      ·
        refine ⟨96916936142492350855118351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64611290761661567236745567 96916936142492350855118351)
        ·
          refine ⟨145375404213738526282677527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96916936142492350855118351 145375404213738526282677527)
          ·
            refine ⟨218063106320607789424016291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145375404213738526282677527 218063106320607789424016291)
            ·
              refine ⟨327094659480911684136024437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218063106320607789424016291 327094659480911684136024437)
              ·
                refine ⟨30665124326335470387752291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 327094659480911684136024437 30665124326335470387752291)
                ·
                  refine ⟨45997686489503205581628437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30665124326335470387752291 45997686489503205581628437)
                  ·
                    refine ⟨2156141554195462761638833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45997686489503205581628437 2156141554195462761638833)
                    ·
                      refine ⟨1617106165646597071229125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2156141554195462761638833 1617106165646597071229125)
                      ·
                        rfl

theorem cell23_3149303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 6, 2].length) (baseStart_3149303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149303 prefixEnd_3149303 := by exact prefixLift 3149303
  have htrace : WordTrace (prefixWord ++ tailWord_3149303) baseStart_3149303 baseEnd_3149303 := by
    simpa [prefixWord, tailWord_3149303, baseEnd_3149303] using wordTrace_append hprefix tailTrace_3149303
  have hstable : (prefixWord ++ tailWord_3149303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149303).length < 2 ^ (prefixWord ++ tailWord_3149303).sum := by decide
  have hdescent : baseEnd_3149303 < baseStart_3149303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149340 : List Nat := [2, 2, 3, 1, 2, 1, 3, 2, 2, 2, 3]
def baseStart_3149340 : Nat := 118140960795 + 3149340 * 2 ^ 59
def prefixEnd_3149340 : Nat := 4983230072969 + 3 ^ 40 * 3149340 * 2
def baseEnd_3149340 : Nat := 1617125164430813426466455

theorem tailTrace_3149340 : CollatzResearch.WordTrace tailWord_3149340 prefixEnd_3149340 1617125164430813426466455 := by
  unfold tailWord_3149340
  simp only [CollatzResearch.WordTrace]
  refine ⟨57432933205243259647766737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76577244273657679530355649 57432933205243259647766737)
  ·
    refine ⟨43074699903932444735825053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57432933205243259647766737 43074699903932444735825053)
    ·
      refine ⟨16153012463974666775934395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43074699903932444735825053 16153012463974666775934395)
      ·
        refine ⟨24229518695962000163901593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16153012463974666775934395 24229518695962000163901593)
        ·
          refine ⟨18172139021971500122926195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24229518695962000163901593 18172139021971500122926195)
          ·
            refine ⟨27258208532957250184389293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18172139021971500122926195 27258208532957250184389293)
            ·
              refine ⟨10221828199858968819145985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27258208532957250184389293 10221828199858968819145985)
              ·
                refine ⟨7666371149894226614359489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10221828199858968819145985 7666371149894226614359489)
                ·
                  refine ⟨5749778362420669960769617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7666371149894226614359489 5749778362420669960769617)
                  ·
                    refine ⟨4312333771815502470577213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5749778362420669960769617 4312333771815502470577213)
                    ·
                      refine ⟨1617125164430813426466455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4312333771815502470577213 1617125164430813426466455)
                      ·
                        rfl

theorem cell23_3149340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_3149340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149340 prefixEnd_3149340 := by exact prefixLift 3149340
  have htrace : WordTrace (prefixWord ++ tailWord_3149340) baseStart_3149340 baseEnd_3149340 := by
    simpa [prefixWord, tailWord_3149340, baseEnd_3149340] using wordTrace_append hprefix tailTrace_3149340
  have hstable : (prefixWord ++ tailWord_3149340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149340).length < 2 ^ (prefixWord ++ tailWord_3149340).sum := by decide
  have hdescent : baseEnd_3149340 < baseStart_3149340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149347 : List Nat := [1, 1, 1, 4, 5, 2, 1, 1, 3, 4]
def baseStart_3149347 : Nat := 118140960795 + 3149347 * 2 ^ 59
def prefixEnd_3149347 : Nat := 4983230072969 + 3 ^ 40 * 3149347 * 2
def baseEnd_3149347 : Nat := 539042919598464966359641

theorem tailTrace_3149347 : CollatzResearch.WordTrace tailWord_3149347 prefixEnd_3149347 539042919598464966359641 := by
  unfold tailWord_3149347
  simp only [CollatzResearch.WordTrace]
  refine ⟨114866121721461159491038295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76577414480974106327358863 114866121721461159491038295)
  ·
    refine ⟨172299182582191739236557443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114866121721461159491038295 172299182582191739236557443)
    ·
      refine ⟨258448773873287608854836165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172299182582191739236557443 258448773873287608854836165)
      ·
        refine ⟨48459145101241426660281781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 258448773873287608854836165 48459145101241426660281781)
        ·
          refine ⟨4543044853241383749401417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48459145101241426660281781 4543044853241383749401417)
          ·
            refine ⟨3407283639931037812051063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4543044853241383749401417 3407283639931037812051063)
            ·
              refine ⟨5110925459896556718076595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3407283639931037812051063 5110925459896556718076595)
              ·
                refine ⟨7666388189844835077114893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5110925459896556718076595 7666388189844835077114893)
                ·
                  refine ⟨2874895571191813153918085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7666388189844835077114893 2874895571191813153918085)
                  ·
                    refine ⟨539042919598464966359641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2874895571191813153918085 539042919598464966359641)
                    ·
                      rfl

theorem cell23_3149347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 3, 4].length) (baseStart_3149347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149347 prefixEnd_3149347 := by exact prefixLift 3149347
  have htrace : WordTrace (prefixWord ++ tailWord_3149347) baseStart_3149347 baseEnd_3149347 := by
    simpa [prefixWord, tailWord_3149347, baseEnd_3149347] using wordTrace_append hprefix tailTrace_3149347
  have hstable : (prefixWord ++ tailWord_3149347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149347).length < 2 ^ (prefixWord ++ tailWord_3149347).sum := by decide
  have hdescent : baseEnd_3149347 < baseStart_3149347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149356 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 1, 11]
def baseStart_3149356 : Nat := 118140960795 + 3149356 * 2 ^ 59
def prefixEnd_3149356 : Nat := 4983230072969 + 3 ^ 40 * 3149356 * 2
def baseEnd_3149356 : Nat := 539044460040428454622127

theorem tailTrace_3149356 : CollatzResearch.WordTrace tailWord_3149356 prefixEnd_3149356 539044460040428454622127 := by
  unfold tailWord_3149356
  simp only [CollatzResearch.WordTrace]
  refine ⟨57433224989214277014057961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76577633318952369352077281 57433224989214277014057961)
  ·
    refine ⟨43074918741910707760543471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57433224989214277014057961 43074918741910707760543471)
    ·
      refine ⟨64612378112866061640815207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43074918741910707760543471 64612378112866061640815207)
      ·
        refine ⟨96918567169299092461222811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64612378112866061640815207 96918567169299092461222811)
        ·
          refine ⟨145377850753948638691834217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96918567169299092461222811 145377850753948638691834217)
          ·
            refine ⟨109033388065461479018875663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145377850753948638691834217 109033388065461479018875663)
            ·
              refine ⟨163550082098192218528313495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109033388065461479018875663 163550082098192218528313495)
              ·
                refine ⟨245325123147288327792470243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163550082098192218528313495 245325123147288327792470243)
                ·
                  refine ⟨367987684720932491688705365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 245325123147288327792470243 367987684720932491688705365)
                  ·
                    refine ⟨539044460040428454622127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 367987684720932491688705365 539044460040428454622127)
                    ·
                      rfl

theorem cell23_3149356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 11].length) (baseStart_3149356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149356 prefixEnd_3149356 := by exact prefixLift 3149356
  have htrace : WordTrace (prefixWord ++ tailWord_3149356) baseStart_3149356 baseEnd_3149356 := by
    simpa [prefixWord, tailWord_3149356, baseEnd_3149356] using wordTrace_append hprefix tailTrace_3149356
  have hstable : (prefixWord ++ tailWord_3149356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149356).length < 2 ^ (prefixWord ++ tailWord_3149356).sum := by decide
  have hdescent : baseEnd_3149356 < baseStart_3149356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149370 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 5, 1, 3]
def baseStart_3149370 : Nat := 118140960795 + 3149370 * 2 ^ 59
def prefixEnd_3149370 : Nat := 4983230072969 + 3 ^ 40 * 3149370 * 2
def baseEnd_3149370 : Nat := 1617140568850448309091317

theorem tailTrace_3149370 : CollatzResearch.WordTrace tailWord_3149370 prefixEnd_3149370 1617140568850448309091317 := by
  unfold tailWord_3149370
  simp only [CollatzResearch.WordTrace]
  refine ⟨28716740150094458604781391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76577973733585222946083709 28716740150094458604781391)
  ·
    refine ⟨43075110225141687907172087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28716740150094458604781391 43075110225141687907172087)
    ·
      refine ⟨64612665337712531860758131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43075110225141687907172087 64612665337712531860758131)
      ·
        refine ⟨96918998006568797791137197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64612665337712531860758131 96918998006568797791137197)
        ·
          refine ⟨36344624252463299171676449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96918998006568797791137197 36344624252463299171676449)
          ·
            refine ⟨27258468189347474378757337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36344624252463299171676449 27258468189347474378757337)
            ·
              refine ⟨20443851142010605784068003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27258468189347474378757337 20443851142010605784068003)
              ·
                refine ⟨30665776713015908676102005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20443851142010605784068003 30665776713015908676102005)
                ·
                  refine ⟨2874916566845241438384563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30665776713015908676102005 2874916566845241438384563)
                  ·
                    refine ⟨4312374850267862157576845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2874916566845241438384563 4312374850267862157576845)
                    ·
                      refine ⟨1617140568850448309091317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4312374850267862157576845 1617140568850448309091317)
                      ·
                        rfl

theorem cell23_3149370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 5, 1, 3].length) (baseStart_3149370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149370 prefixEnd_3149370 := by exact prefixLift 3149370
  have htrace : WordTrace (prefixWord ++ tailWord_3149370) baseStart_3149370 baseEnd_3149370 := by
    simpa [prefixWord, tailWord_3149370, baseEnd_3149370] using wordTrace_append hprefix tailTrace_3149370
  have hstable : (prefixWord ++ tailWord_3149370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149370).length < 2 ^ (prefixWord ++ tailWord_3149370).sum := by decide
  have hdescent : baseEnd_3149370 < baseStart_3149370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149387 : List Nat := [1, 1, 1, 1, 3, 1, 3, 7, 1, 1, 3]
def baseStart_3149387 : Nat := 118140960795 + 3149387 * 2 ^ 59
def prefixEnd_3149387 : Nat := 4983230072969 + 3 ^ 40 * 3149387 * 2
def baseEnd_3149387 : Nat := 1617149298021574742578739

theorem tailTrace_3149387 : CollatzResearch.WordTrace tailWord_3149387 prefixEnd_3149387 1617149298021574742578739 := by
  unfold tailWord_3149387
  simp only [CollatzResearch.WordTrace]
  refine ⟨114867580641316246322494415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76578387094210830881662943 114867580641316246322494415)
  ·
    refine ⟨172301370961974369483741623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114867580641316246322494415 172301370961974369483741623)
    ·
      refine ⟨258452056442961554225612435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172301370961974369483741623 258452056442961554225612435)
      ·
        refine ⟨387678084664442331338418653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258452056442961554225612435 387678084664442331338418653)
        ·
          refine ⟨145379281749165874251906995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 387678084664442331338418653 145379281749165874251906995)
          ·
            refine ⟨218068922623748811377860493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145379281749165874251906995 218068922623748811377860493)
            ·
              refine ⟨81775845983905804266697685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 218068922623748811377860493 81775845983905804266697685)
              ·
                refine ⟨1916621390247792287500727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 81775845983905804266697685 1916621390247792287500727)
                ·
                  refine ⟨2874932085371688431251091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1916621390247792287500727 2874932085371688431251091)
                  ·
                    refine ⟨4312398128057532646876637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2874932085371688431251091 4312398128057532646876637)
                    ·
                      refine ⟨1617149298021574742578739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4312398128057532646876637 1617149298021574742578739)
                      ·
                        rfl

theorem cell23_3149387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7, 1, 1, 3].length) (baseStart_3149387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149387 prefixEnd_3149387 := by exact prefixLift 3149387
  have htrace : WordTrace (prefixWord ++ tailWord_3149387) baseStart_3149387 baseEnd_3149387 := by
    simpa [prefixWord, tailWord_3149387, baseEnd_3149387] using wordTrace_append hprefix tailTrace_3149387
  have hstable : (prefixWord ++ tailWord_3149387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149387).length < 2 ^ (prefixWord ++ tailWord_3149387).sum := by decide
  have hdescent : baseEnd_3149387 < baseStart_3149387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149398 : List Nat := [5, 2, 2, 2, 1, 1, 1, 4, 1, 4]
def baseStart_3149398 : Nat := 118140960795 + 3149398 * 2 ^ 59
def prefixEnd_3149398 : Nat := 4983230072969 + 3 ^ 40 * 3149398 * 2
def baseEnd_3149398 : Nat := 539051648769591399847063

theorem tailTrace_3149398 : CollatzResearch.WordTrace tailWord_3149398 prefixEnd_3149398 539051648769591399847063 := by
  unfold tailWord_3149398
  simp only [CollatzResearch.WordTrace]
  refine ⟨7179248865267274700071553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76578654562850930134096565 7179248865267274700071553)
  ·
    refine ⟨5384436648950456025053665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7179248865267274700071553 5384436648950456025053665)
    ·
      refine ⟨4038327486712842018790249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5384436648950456025053665 4038327486712842018790249)
      ·
        refine ⟨3028745615034631514092687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4038327486712842018790249 3028745615034631514092687)
        ·
          refine ⟨4543118422551947271139031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3028745615034631514092687 4543118422551947271139031)
          ·
            refine ⟨6814677633827920906708547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4543118422551947271139031 6814677633827920906708547)
            ·
              refine ⟨10222016450741881360062821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6814677633827920906708547 10222016450741881360062821)
              ·
                refine ⟨1916628084514102755011779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10222016450741881360062821 1916628084514102755011779)
                ·
                  refine ⟨2874942126771154132517669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1916628084514102755011779 2874942126771154132517669)
                  ·
                    refine ⟨539051648769591399847063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2874942126771154132517669 539051648769591399847063)
                    ·
                      rfl

theorem cell23_3149398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_3149398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149398 prefixEnd_3149398 := by exact prefixLift 3149398
  have htrace : WordTrace (prefixWord ++ tailWord_3149398) baseStart_3149398 baseEnd_3149398 := by
    simpa [prefixWord, tailWord_3149398, baseEnd_3149398] using wordTrace_append hprefix tailTrace_3149398
  have hstable : (prefixWord ++ tailWord_3149398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149398).length < 2 ^ (prefixWord ++ tailWord_3149398).sum := by decide
  have hdescent : baseEnd_3149398 < baseStart_3149398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149447 : List Nat := [1, 1, 4, 2, 1, 4, 1, 3, 1, 2, 3]
def baseStart_3149447 : Nat := 118140960795 + 3149447 * 2 ^ 59
def prefixEnd_3149447 : Nat := 4983230072969 + 3 ^ 40 * 3149447 * 2
def baseEnd_3149447 : Nat := 1617180106860844507828463

theorem tailTrace_3149447 : CollatzResearch.WordTrace tailWord_3149447 prefixEnd_3149447 1617180106860844507828463 := by
  unfold tailWord_3149447
  simp only [CollatzResearch.WordTrace]
  refine ⟨114869769021098876569678595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76579846014065917713119063 114869769021098876569678595)
  ·
    refine ⟨172304653531648314854517893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114869769021098876569678595 172304653531648314854517893)
    ·
      refine ⟨32307122537184059035222105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172304653531648314854517893 32307122537184059035222105)
      ·
        refine ⟨24230341902888044276416579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32307122537184059035222105 24230341902888044276416579)
        ·
          refine ⟨36345512854332066414624869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24230341902888044276416579 36345512854332066414624869)
          ·
            refine ⟨6814783660187262452742163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36345512854332066414624869 6814783660187262452742163)
            ·
              refine ⟨10222175490280893679113245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6814783660187262452742163 10222175490280893679113245)
              ·
                refine ⟨3833315808855335129667467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10222175490280893679113245 3833315808855335129667467)
                ·
                  refine ⟨5749973713283002694501201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3833315808855335129667467 5749973713283002694501201)
                  ·
                    refine ⟨4312480284962252020875901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5749973713283002694501201 4312480284962252020875901)
                    ·
                      refine ⟨1617180106860844507828463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4312480284962252020875901 1617180106860844507828463)
                      ·
                        rfl

theorem cell23_3149447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_3149447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149447 prefixEnd_3149447 := by exact prefixLift 3149447
  have htrace : WordTrace (prefixWord ++ tailWord_3149447) baseStart_3149447 baseEnd_3149447 := by
    simpa [prefixWord, tailWord_3149447, baseEnd_3149447] using wordTrace_append hprefix tailTrace_3149447
  have hstable : (prefixWord ++ tailWord_3149447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149447).length < 2 ^ (prefixWord ++ tailWord_3149447).sum := by decide
  have hdescent : baseEnd_3149447 < baseStart_3149447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149454 : List Nat := [4, 1, 1, 3, 1, 4, 1, 2, 2, 4]
def baseStart_3149454 : Nat := 118140960795 + 3149454 * 2 ^ 59
def prefixEnd_3149454 : Nat := 4983230072969 + 3 ^ 40 * 3149454 * 2
def baseEnd_3149454 : Nat := 539061233741808660146977

theorem tailTrace_3149454 : CollatzResearch.WordTrace tailWord_3149454 prefixEnd_3149454 539061233741808660146977 := by
  unfold tailWord_3149454
  simp only [CollatzResearch.WordTrace]
  refine ⟨14358753041509189595647927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76580016221382344510122277 14358753041509189595647927)
  ·
    refine ⟨21538129562263784393471891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14358753041509189595647927 21538129562263784393471891)
    ·
      refine ⟨32307194343395676590207837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21538129562263784393471891 32307194343395676590207837)
      ·
        refine ⟨12115197878773378721327939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32307194343395676590207837 12115197878773378721327939)
        ·
          refine ⟨18172796818160068081991909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12115197878773378721327939 18172796818160068081991909)
          ·
            refine ⟨3407399403405012765373483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18172796818160068081991909 3407399403405012765373483)
            ·
              refine ⟨5111099105107519148060225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3407399403405012765373483 5111099105107519148060225)
              ·
                refine ⟨3833324328830639361045169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5111099105107519148060225 3833324328830639361045169)
                ·
                  refine ⟨2874993246622979520783877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3833324328830639361045169 2874993246622979520783877)
                  ·
                    refine ⟨539061233741808660146977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2874993246622979520783877 539061233741808660146977)
                    ·
                      rfl

theorem cell23_3149454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_3149454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149454 prefixEnd_3149454 := by exact prefixLift 3149454
  have htrace : WordTrace (prefixWord ++ tailWord_3149454) baseStart_3149454 baseEnd_3149454 := by
    simpa [prefixWord, tailWord_3149454, baseEnd_3149454] using wordTrace_append hprefix tailTrace_3149454
  have hstable : (prefixWord ++ tailWord_3149454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149454).length < 2 ^ (prefixWord ++ tailWord_3149454).sum := by decide
  have hdescent : baseEnd_3149454 < baseStart_3149454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149471 : List Nat := [1, 1, 2, 7, 1, 1, 3, 1, 2, 4]
def baseStart_3149471 : Nat := 118140960795 + 3149471 * 2 ^ 59
def prefixEnd_3149471 : Nat := 4983230072969 + 3 ^ 40 * 3149471 * 2
def baseEnd_3149471 : Nat := 539064143465517471309451

theorem tailTrace_3149471 : CollatzResearch.WordTrace tailWord_3149471 prefixEnd_3149471 539064143465517471309451 := by
  unfold tailWord_3149471
  simp only [CollatzResearch.WordTrace]
  refine ⟨114870644373011928668552267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76580429582007952445701511 114870644373011928668552267)
  ·
    refine ⟨172305966559517893002828401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114870644373011928668552267 172305966559517893002828401)
    ·
      refine ⟨129229474919638419752121301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172305966559517893002828401 129229474919638419752121301)
      ·
        refine ⟨3028815818429025462940343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 129229474919638419752121301 3028815818429025462940343)
        ·
          refine ⟨4543223727643538194410515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3028815818429025462940343 4543223727643538194410515)
          ·
            refine ⟨6814835591465307291615773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4543223727643538194410515 6814835591465307291615773)
            ·
              refine ⟨2555563346799490234355915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6814835591465307291615773 2555563346799490234355915)
              ·
                refine ⟨3833345020199235351533873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2555563346799490234355915 3833345020199235351533873)
                ·
                  refine ⟨2875008765149426513650405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3833345020199235351533873 2875008765149426513650405)
                  ·
                    refine ⟨539064143465517471309451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2875008765149426513650405 539064143465517471309451)
                    ·
                      rfl

theorem cell23_3149471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 2, 4].length) (baseStart_3149471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149471 prefixEnd_3149471 := by exact prefixLift 3149471
  have htrace : WordTrace (prefixWord ++ tailWord_3149471) baseStart_3149471 baseEnd_3149471 := by
    simpa [prefixWord, tailWord_3149471, baseEnd_3149471] using wordTrace_append hprefix tailTrace_3149471
  have hstable : (prefixWord ++ tailWord_3149471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149471).length < 2 ^ (prefixWord ++ tailWord_3149471).sum := by decide
  have hdescent : baseEnd_3149471 < baseStart_3149471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149477 : List Nat := [1, 3, 1, 2, 1, 2, 2, 5, 2, 1, 3]
def baseStart_3149477 : Nat := 118140960795 + 3149477 * 2 ^ 59
def prefixEnd_3149477 : Nat := 4983230072969 + 3 ^ 40 * 3149477 * 2
def baseEnd_3149477 : Nat := 1617195511280479390453325

theorem tailTrace_3149477 : CollatzResearch.WordTrace tailWord_3149477 prefixEnd_3149477 1617195511280479390453325 := by
  unfold tailWord_3149477
  simp only [CollatzResearch.WordTrace]
  refine ⟨114870863210990191693270685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76580575473993461128847123 114870863210990191693270685)
  ·
    refine ⟨43076573704121321884976507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114870863210990191693270685 43076573704121321884976507)
    ·
      refine ⟨64614860556181982827464761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43076573704121321884976507 64614860556181982827464761)
      ·
        refine ⟨48461145417136487120598571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64614860556181982827464761 48461145417136487120598571)
        ·
          refine ⟨72691718125704730680897857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48461145417136487120598571 72691718125704730680897857)
          ·
            refine ⟨54518788594278548010673393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72691718125704730680897857 54518788594278548010673393)
            ·
              refine ⟨40889091445708911008005045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54518788594278548010673393 40889091445708911008005045)
              ·
                refine ⟨3833352323035210407000473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40889091445708911008005045 3833352323035210407000473)
                ·
                  refine ⟨2875014242276407805250355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3833352323035210407000473 2875014242276407805250355)
                  ·
                    refine ⟨4312521363414611707875533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2875014242276407805250355 4312521363414611707875533)
                    ·
                      refine ⟨1617195511280479390453325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4312521363414611707875533 1617195511280479390453325)
                      ·
                        rfl

theorem cell23_3149477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_3149477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149477 prefixEnd_3149477 := by exact prefixLift 3149477
  have htrace : WordTrace (prefixWord ++ tailWord_3149477) baseStart_3149477 baseEnd_3149477 := by
    simpa [prefixWord, tailWord_3149477, baseEnd_3149477] using wordTrace_append hprefix tailTrace_3149477
  have hstable : (prefixWord ++ tailWord_3149477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149477).length < 2 ^ (prefixWord ++ tailWord_3149477).sum := by decide
  have hdescent : baseEnd_3149477 < baseStart_3149477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149580 : List Nat := [2, 2, 1, 2, 2, 1, 4, 1, 1, 2, 5]
def baseStart_3149580 : Nat := 118140960795 + 3149580 * 2 ^ 59
def prefixEnd_3149580 : Nat := 4983230072969 + 3 ^ 40 * 3149580 * 2
def baseEnd_3149580 : Nat := 1617248399787892487465351

theorem tailTrace_3149580 : CollatzResearch.WordTrace tailWord_3149580 prefixEnd_3149580 1617248399787892487465351 := by
  unfold tailWord_3149580
  simp only [CollatzResearch.WordTrace]
  refine ⟨57437309964808520142135097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76583079953078026856180129 57437309964808520142135097)
  ·
    refine ⟨43077982473606390106601323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57437309964808520142135097 43077982473606390106601323)
    ·
      refine ⟨64616973710409585159901985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43077982473606390106601323 64616973710409585159901985)
      ·
        refine ⟨48462730282807188869926489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64616973710409585159901985 48462730282807188869926489)
        ·
          refine ⟨36347047712105391652444867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48462730282807188869926489 36347047712105391652444867)
          ·
            refine ⟨54520571568158087478667301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36347047712105391652444867 54520571568158087478667301)
            ·
              refine ⟨10222607169029641402250119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54520571568158087478667301 10222607169029641402250119)
              ·
                refine ⟨15333910753544462103375179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10222607169029641402250119 15333910753544462103375179)
                ·
                  refine ⟨23000866130316693155062769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15333910753544462103375179 23000866130316693155062769)
                  ·
                    refine ⟨17250649597737519866297077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23000866130316693155062769 17250649597737519866297077)
                    ·
                      refine ⟨1617248399787892487465351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17250649597737519866297077 1617248399787892487465351)
                      ·
                        rfl

theorem cell23_3149580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_3149580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149580 prefixEnd_3149580 := by exact prefixLift 3149580
  have htrace : WordTrace (prefixWord ++ tailWord_3149580) baseStart_3149580 baseEnd_3149580 := by
    simpa [prefixWord, tailWord_3149580, baseEnd_3149580] using wordTrace_append hprefix tailTrace_3149580
  have hstable : (prefixWord ++ tailWord_3149580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149580).length < 2 ^ (prefixWord ++ tailWord_3149580).sum := by decide
  have hdescent : baseEnd_3149580 < baseStart_3149580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149604 : List Nat := [2, 3, 1, 3, 2, 3, 1, 1, 2, 5]
def baseStart_3149604 : Nat := 118140960795 + 3149604 * 2 ^ 59
def prefixEnd_3149604 : Nat := 4983230072969 + 3 ^ 40 * 3149604 * 2
def baseEnd_3149604 : Nat := 539086907774533464521747

theorem tailTrace_3149604 : CollatzResearch.WordTrace tailWord_3149604 prefixEnd_3149604 539086907774533464521747 := by
  unfold tailWord_3149604
  simp only [CollatzResearch.WordTrace]
  refine ⟨57437747640765046191571933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76583663521020061588762577 57437747640765046191571933)
  ·
    refine ⟨21539155365286892321839475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57437747640765046191571933 21539155365286892321839475)
    ·
      refine ⟨32308733047930338482759213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21539155365286892321839475 32308733047930338482759213)
      ·
        refine ⟨12115774892973876931034705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32308733047930338482759213 12115774892973876931034705)
        ·
          refine ⟨9086831169730407698276029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12115774892973876931034705 9086831169730407698276029)
          ·
            refine ⟨3407561688648902886853511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9086831169730407698276029 3407561688648902886853511)
            ·
              refine ⟨5111342532973354330280267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3407561688648902886853511 5111342532973354330280267)
              ·
                refine ⟨7667013799460031495420401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5111342532973354330280267 7667013799460031495420401)
                ·
                  refine ⟨5750260349595023621565301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7667013799460031495420401 5750260349595023621565301)
                  ·
                    refine ⟨539086907774533464521747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5750260349595023621565301 539086907774533464521747)
                    ·
                      rfl

theorem cell23_3149604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_3149604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149604 prefixEnd_3149604 := by exact prefixLift 3149604
  have htrace : WordTrace (prefixWord ++ tailWord_3149604) baseStart_3149604 baseEnd_3149604 := by
    simpa [prefixWord, tailWord_3149604, baseEnd_3149604] using wordTrace_append hprefix tailTrace_3149604
  have hstable : (prefixWord ++ tailWord_3149604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149604).length < 2 ^ (prefixWord ++ tailWord_3149604).sum := by decide
  have hdescent : baseEnd_3149604 < baseStart_3149604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149668 : List Nat := [2, 3, 1, 1, 5, 2, 1, 3, 1, 4]
def baseStart_3149668 : Nat := 118140960795 + 3149668 * 2 ^ 59
def prefixEnd_3149668 : Nat := 4983230072969 + 3 ^ 40 * 3149668 * 2
def baseEnd_3149668 : Nat := 539097862028496047721649

theorem tailTrace_3149668 : CollatzResearch.WordTrace tailWord_3149668 prefixEnd_3149668 539097862028496047721649 := by
  unfold tailWord_3149668
  simp only [CollatzResearch.WordTrace]
  refine ⟨57438914776649115656736829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76585219702198820875649105 57438914776649115656736829)
  ·
    refine ⟨21539593041243418371276311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57438914776649115656736829 21539593041243418371276311)
    ·
      refine ⟨32309389561865127556914467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21539593041243418371276311 32309389561865127556914467)
      ·
        refine ⟨48464084342797691335371701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32309389561865127556914467 48464084342797691335371701)
        ·
          refine ⟨4543507907137283562691097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48464084342797691335371701 4543507907137283562691097)
          ·
            refine ⟨3407630930352962672018323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4543507907137283562691097 3407630930352962672018323)
            ·
              refine ⟨5111446395529444008027485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3407630930352962672018323 5111446395529444008027485)
              ·
                refine ⟨1916792398323541503010307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5111446395529444008027485 1916792398323541503010307)
                ·
                  refine ⟨2875188597485312254515461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1916792398323541503010307 2875188597485312254515461)
                  ·
                    refine ⟨539097862028496047721649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2875188597485312254515461 539097862028496047721649)
                    ·
                      rfl

theorem cell23_3149668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_3149668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149668 prefixEnd_3149668 := by exact prefixLift 3149668
  have htrace : WordTrace (prefixWord ++ tailWord_3149668) baseStart_3149668 baseEnd_3149668 := by
    simpa [prefixWord, tailWord_3149668, baseEnd_3149668] using wordTrace_append hprefix tailTrace_3149668
  have hstable : (prefixWord ++ tailWord_3149668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149668).length < 2 ^ (prefixWord ++ tailWord_3149668).sum := by decide
  have hdescent : baseEnd_3149668 < baseStart_3149668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149724 : List Nat := [2, 2, 3, 3, 1, 2, 1, 2, 1, 6]
def baseStart_3149724 : Nat := 118140960795 + 3149724 * 2 ^ 59
def prefixEnd_3149724 : Nat := 4983230072969 + 3 ^ 40 * 3149724 * 2
def baseEnd_3149724 : Nat := 539107447000713308021563

theorem tailTrace_3149724 : CollatzResearch.WordTrace tailWord_3149724 prefixEnd_3149724 539107447000713308021563 := by
  unfold tailWord_3149724
  simp only [CollatzResearch.WordTrace]
  refine ⟨57439936020547676438756113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76586581360730235251674817 57439936020547676438756113)
  ·
    refine ⟨43079952015410757329067085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57439936020547676438756113 43079952015410757329067085)
    ·
      refine ⟨16154982005779033998400157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43079952015410757329067085 16154982005779033998400157)
      ·
        refine ⟨6058118252167137749400059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16154982005779033998400157 6058118252167137749400059)
        ·
          refine ⟨9087177378250706624100089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6058118252167137749400059 9087177378250706624100089)
          ·
            refine ⟨6815383033688029968075067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9087177378250706624100089 6815383033688029968075067)
            ·
              refine ⟨10223074550532044952112601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6815383033688029968075067 10223074550532044952112601)
              ·
                refine ⟨7667305912899033714084451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10223074550532044952112601 7667305912899033714084451)
                ·
                  refine ⟨11500958869348550571126677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7667305912899033714084451 11500958869348550571126677)
                  ·
                    refine ⟨539107447000713308021563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11500958869348550571126677 539107447000713308021563)
                    ·
                      rfl

theorem cell23_3149724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_3149724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149724 prefixEnd_3149724 := by exact prefixLift 3149724
  have htrace : WordTrace (prefixWord ++ tailWord_3149724) baseStart_3149724 baseEnd_3149724 := by
    simpa [prefixWord, tailWord_3149724, baseEnd_3149724] using wordTrace_append hprefix tailTrace_3149724
  have hstable : (prefixWord ++ tailWord_3149724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149724).length < 2 ^ (prefixWord ++ tailWord_3149724).sum := by decide
  have hdescent : baseEnd_3149724 < baseStart_3149724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149747 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 3, 3, 3]
def baseStart_3149747 : Nat := 118140960795 + 3149747 * 2 ^ 59
def prefixEnd_3149747 : Nat := 4983230072969 + 3 ^ 40 * 3149747 * 2
def baseEnd_3149747 : Nat := 1617334151057193334077083

theorem tailTrace_3149747 : CollatzResearch.WordTrace tailWord_3149747 prefixEnd_3149747 1617334151057193334077083 := by
  unfold tailWord_3149747
  simp only [CollatzResearch.WordTrace]
  refine ⟨114880710920012027805599495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76587140613341351870399663 114880710920012027805599495)
  ·
    refine ⟨172321066380018041708399243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114880710920012027805599495 172321066380018041708399243)
    ·
      refine ⟨258481599570027062562598865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172321066380018041708399243 258481599570027062562598865)
      ·
        refine ⟨193861199677520296921949149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258481599570027062562598865 193861199677520296921949149)
        ·
          refine ⟨72697949879070111345730931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193861199677520296921949149 72697949879070111345730931)
          ·
            refine ⟨109046924818605167018596397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72697949879070111345730931 109046924818605167018596397)
            ·
              refine ⟨40892596806976937631973649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109046924818605167018596397 40892596806976937631973649)
              ·
                refine ⟨30669447605232703223980237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40892596806976937631973649 30669447605232703223980237)
                ·
                  refine ⟨11501042851962263708992589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30669447605232703223980237 11501042851962263708992589)
                  ·
                    refine ⟨4312891069485848890872221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11501042851962263708992589 4312891069485848890872221)
                    ·
                      refine ⟨1617334151057193334077083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4312891069485848890872221 1617334151057193334077083)
                      ·
                        rfl

theorem cell23_3149747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 3, 3].length) (baseStart_3149747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149747 prefixEnd_3149747 := by exact prefixLift 3149747
  have htrace : WordTrace (prefixWord ++ tailWord_3149747) baseStart_3149747 baseEnd_3149747 := by
    simpa [prefixWord, tailWord_3149747, baseEnd_3149747] using wordTrace_append hprefix tailTrace_3149747
  have hstable : (prefixWord ++ tailWord_3149747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149747).length < 2 ^ (prefixWord ++ tailWord_3149747).sum := by decide
  have hdescent : baseEnd_3149747 < baseStart_3149747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149782 : List Nat := [5, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4]
def baseStart_3149782 : Nat := 118140960795 + 3149782 * 2 ^ 59
def prefixEnd_3149782 : Nat := 4983230072969 + 3 ^ 40 * 3149782 * 2
def baseEnd_3149782 : Nat := 1617352122880100697139423

theorem tailTrace_3149782 : CollatzResearch.WordTrace tailWord_3149782 prefixEnd_3149782 1617352122880100697139423 := by
  unfold tailWord_3149782
  simp only [CollatzResearch.WordTrace]
  refine ⟨7180124217180326798945225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76587991649923485855415733 7180124217180326798945225)
  ·
    refine ⟨5385093162885245099208919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7180124217180326798945225 5385093162885245099208919)
    ·
      refine ⟨8077639744327867648813379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5385093162885245099208919 8077639744327867648813379)
      ·
        refine ⟨12116459616491801473220069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8077639744327867648813379 12116459616491801473220069)
        ·
          refine ⟨2271836178092212776228763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12116459616491801473220069 2271836178092212776228763)
          ·
            refine ⟨3407754267138319164343145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2271836178092212776228763 3407754267138319164343145)
            ·
              refine ⟨2555815700353739373257359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3407754267138319164343145 2555815700353739373257359)
              ·
                refine ⟨3833723550530609059886039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2555815700353739373257359 3833723550530609059886039)
                ·
                  refine ⟨5750585325795913589829059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3833723550530609059886039 5750585325795913589829059)
                  ·
                    refine ⟨8625877988693870384743589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5750585325795913589829059 8625877988693870384743589)
                    ·
                      refine ⟨1617352122880100697139423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8625877988693870384743589 1617352122880100697139423)
                      ·
                        rfl

theorem cell23_3149782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_3149782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149782 prefixEnd_3149782 := by exact prefixLift 3149782
  have htrace : WordTrace (prefixWord ++ tailWord_3149782) baseStart_3149782 baseEnd_3149782 := by
    simpa [prefixWord, tailWord_3149782, baseEnd_3149782] using wordTrace_append hprefix tailTrace_3149782
  have hstable : (prefixWord ++ tailWord_3149782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149782).length < 2 ^ (prefixWord ++ tailWord_3149782).sum := by decide
  have hdescent : baseEnd_3149782 < baseStart_3149782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149785 : List Nat := [1, 2, 1, 2, 7, 1, 2, 1, 1, 2, 3]
def baseStart_3149785 : Nat := 118140960795 + 3149785 * 2 ^ 59
def prefixEnd_3149785 : Nat := 4983230072969 + 3 ^ 40 * 3149785 * 2
def baseEnd_3149785 : Nat := 1617353663322064185401909

theorem tailTrace_3149785 : CollatzResearch.WordTrace tailWord_3149785 prefixEnd_3149785 1617353663322064185401909 := by
  unfold tailWord_3149785
  simp only [CollatzResearch.WordTrace]
  refine ⟨114882096893874360295482809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76588064595916240196988539 114882096893874360295482809)
  ·
    refine ⟨86161572670405770221612107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114882096893874360295482809 86161572670405770221612107)
    ·
      refine ⟨129242359005608655332418161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86161572670405770221612107 129242359005608655332418161)
      ·
        refine ⟨96931769254206491499313621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129242359005608655332418161 96931769254206491499313621)
        ·
          refine ⟨2271838341895464644515163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 96931769254206491499313621 2271838341895464644515163)
          ·
            refine ⟨3407757512843196966772745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2271838341895464644515163 3407757512843196966772745)
            ·
              refine ⟨2555818134632397725079559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3407757512843196966772745 2555818134632397725079559)
              ·
                refine ⟨3833727201948596587619339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2555818134632397725079559 3833727201948596587619339)
                ·
                  refine ⟨5750590802922894881429009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3833727201948596587619339 5750590802922894881429009)
                  ·
                    refine ⟨4312943102192171161071757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5750590802922894881429009 4312943102192171161071757)
                    ·
                      refine ⟨1617353663322064185401909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4312943102192171161071757 1617353663322064185401909)
                      ·
                        rfl

theorem cell23_3149785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 1, 2, 3].length) (baseStart_3149785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149785 prefixEnd_3149785 := by exact prefixLift 3149785
  have htrace : WordTrace (prefixWord ++ tailWord_3149785) baseStart_3149785 baseEnd_3149785 := by
    simpa [prefixWord, tailWord_3149785, baseEnd_3149785] using wordTrace_append hprefix tailTrace_3149785
  have hstable : (prefixWord ++ tailWord_3149785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149785).length < 2 ^ (prefixWord ++ tailWord_3149785).sum := by decide
  have hdescent : baseEnd_3149785 < baseStart_3149785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149804 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 3, 4, 2]
def baseStart_3149804 : Nat := 118140960795 + 3149804 * 2 ^ 59
def prefixEnd_3149804 : Nat := 4983230072969 + 3 ^ 40 * 3149804 * 2
def baseEnd_3149804 : Nat := 1617363419454499611064321

theorem tailTrace_3149804 : CollatzResearch.WordTrace tailWord_3149804 prefixEnd_3149804 1617363419454499611064321 := by
  unfold tailWord_3149804
  simp only [CollatzResearch.WordTrace]
  refine ⟨57441394940402763270212233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76588526587203684360282977 57441394940402763270212233)
  ·
    refine ⟨43081046205302072452659175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57441394940402763270212233 43081046205302072452659175)
    ·
      refine ⟨64621569307953108678988763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43081046205302072452659175 64621569307953108678988763)
      ·
        refine ⟨96932353961929663018483145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64621569307953108678988763 96932353961929663018483145)
        ·
          refine ⟨72699265471447247263862359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96932353961929663018483145 72699265471447247263862359)
          ·
            refine ⟨109048898207170870895793539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72699265471447247263862359 109048898207170870895793539)
            ·
              refine ⟨163573347310756306343690309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109048898207170870895793539 163573347310756306343690309)
              ·
                refine ⟨30670002620766807439441933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163573347310756306343690309 30670002620766807439441933)
                ·
                  refine ⟨11501250982787552789790725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30670002620766807439441933 11501250982787552789790725)
                  ·
                    refine ⟨2156484559272666148085761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11501250982787552789790725 2156484559272666148085761)
                    ·
                      refine ⟨1617363419454499611064321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2156484559272666148085761 1617363419454499611064321)
                      ·
                        rfl

theorem cell23_3149804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 4, 2].length) (baseStart_3149804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149804 prefixEnd_3149804 := by exact prefixLift 3149804
  have htrace : WordTrace (prefixWord ++ tailWord_3149804) baseStart_3149804 baseEnd_3149804 := by
    simpa [prefixWord, tailWord_3149804, baseEnd_3149804] using wordTrace_append hprefix tailTrace_3149804
  have hstable : (prefixWord ++ tailWord_3149804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149804).length < 2 ^ (prefixWord ++ tailWord_3149804).sum := by decide
  have hdescent : baseEnd_3149804 < baseStart_3149804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149821 : List Nat := [1, 4, 1, 1, 1, 2, 5, 1, 1, 4, 2]
def baseStart_3149821 : Nat := 118140960795 + 3149821 * 2 ^ 59
def prefixEnd_3149821 : Nat := 4983230072969 + 3 ^ 40 * 3149821 * 2
def baseEnd_3149821 : Nat := 1617372148625626044551743

theorem tailTrace_3149821 : CollatzResearch.WordTrace tailWord_3149821 prefixEnd_3149821 1617372148625626044551743 := by
  unfold tailWord_3149821
  simp only [CollatzResearch.WordTrace]
  refine ⟨114883409921743938443793317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76588939947829292295862211 114883409921743938443793317)
  ·
    refine ⟨21540639360326988458211247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114883409921743938443793317 21540639360326988458211247)
    ·
      refine ⟨32310959040490482687316871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21540639360326988458211247 32310959040490482687316871)
      ·
        refine ⟨48466438560735724030975307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32310959040490482687316871 48466438560735724030975307)
        ·
          refine ⟨72699657841103586046462961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48466438560735724030975307 72699657841103586046462961)
          ·
            refine ⟨54524743380827689534847221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72699657841103586046462961 54524743380827689534847221)
            ·
              refine ⟨5111694691952595893891927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54524743380827689534847221 5111694691952595893891927)
              ·
                refine ⟨7667542037928893840837891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5111694691952595893891927 7667542037928893840837891)
                ·
                  refine ⟨11501313056893340761256837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7667542037928893840837891 11501313056893340761256837)
                  ·
                    refine ⟨2156496198167501392735657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11501313056893340761256837 2156496198167501392735657)
                    ·
                      refine ⟨1617372148625626044551743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2156496198167501392735657 1617372148625626044551743)
                      ·
                        rfl

theorem cell23_3149821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 4, 2].length) (baseStart_3149821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149821 prefixEnd_3149821 := by exact prefixLift 3149821
  have htrace : WordTrace (prefixWord ++ tailWord_3149821) baseStart_3149821 baseEnd_3149821 := by
    simpa [prefixWord, tailWord_3149821, baseEnd_3149821] using wordTrace_append hprefix tailTrace_3149821
  have hstable : (prefixWord ++ tailWord_3149821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149821).length < 2 ^ (prefixWord ++ tailWord_3149821).sum := by decide
  have hdescent : baseEnd_3149821 < baseStart_3149821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149887 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 2, 8]
def baseStart_3149887 : Nat := 118140960795 + 3149887 * 2 ^ 59
def prefixEnd_3149887 : Nat := 4983230072969 + 3 ^ 40 * 3149887 * 2
def baseEnd_3149887 : Nat := 539135346116274262108813

theorem tailTrace_3149887 : CollatzResearch.WordTrace tailWord_3149887 prefixEnd_3149887 539135346116274262108813 := by
  unfold tailWord_3149887
  simp only [CollatzResearch.WordTrace]
  refine ⟨114885817139504831715695915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76590544759669887810463943 114885817139504831715695915)
  ·
    refine ⟨172328725709257247573543873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114885817139504831715695915 172328725709257247573543873)
    ·
      refine ⟨129246544281942935680157905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172328725709257247573543873 129246544281942935680157905)
      ·
        refine ⟨96934908211457201760118429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129246544281942935680157905 96934908211457201760118429)
        ·
          refine ⟨36350590579296450660044411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96934908211457201760118429 36350590579296450660044411)
          ·
            refine ⟨54525885868944675990066617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36350590579296450660044411 54525885868944675990066617)
            ·
              refine ⟨40894414401708506992549963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54525885868944675990066617 40894414401708506992549963)
              ·
                refine ⟨61341621602562760488824945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40894414401708506992549963 61341621602562760488824945)
                ·
                  refine ⟨46006216201922070366618709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61341621602562760488824945 46006216201922070366618709)
                  ·
                    refine ⟨539135346116274262108813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46006216201922070366618709 539135346116274262108813)
                    ·
                      rfl

theorem cell23_3149887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 8].length) (baseStart_3149887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149887 prefixEnd_3149887 := by exact prefixLift 3149887
  have htrace : WordTrace (prefixWord ++ tailWord_3149887) baseStart_3149887 baseEnd_3149887 := by
    simpa [prefixWord, tailWord_3149887, baseEnd_3149887] using wordTrace_append hprefix tailTrace_3149887
  have hstable : (prefixWord ++ tailWord_3149887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149887).length < 2 ^ (prefixWord ++ tailWord_3149887).sum := by decide
  have hdescent : baseEnd_3149887 < baseStart_3149887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149948 : List Nat := [2, 2, 2, 1, 1, 6, 1, 1, 2, 2, 3]
def baseStart_3149948 : Nat := 118140960795 + 3149948 * 2 ^ 59
def prefixEnd_3149948 : Nat := 4983230072969 + 3 ^ 40 * 3149948 * 2
def baseEnd_3149948 : Nat := 1617437360668747047663659

theorem tailTrace_3149948 : CollatzResearch.WordTrace tailWord_3149948 prefixEnd_3149948 1617437360668747047663659 := by
  unfold tailWord_3149948
  simp only [CollatzResearch.WordTrace]
  refine ⟨57444020996141919566833249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76592027994855892755777665 57444020996141919566833249)
  ·
    refine ⟨43083015747106439675124937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57444020996141919566833249 43083015747106439675124937)
    ·
      refine ⟨32312261810329829756343703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43083015747106439675124937 32312261810329829756343703)
      ·
        refine ⟨48468392715494744634515555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32312261810329829756343703 48468392715494744634515555)
        ·
          refine ⟨72702589073242116951773333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48468392715494744634515555 72702589073242116951773333)
          ·
            refine ⟨3407933862808224232114375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72702589073242116951773333 3407933862808224232114375)
            ·
              refine ⟨5111900794212336348171563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3407933862808224232114375 5111900794212336348171563)
              ·
                refine ⟨7667851191318504522257345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5111900794212336348171563 7667851191318504522257345)
                ·
                  refine ⟨5750888393488878391693009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7667851191318504522257345 5750888393488878391693009)
                  ·
                    refine ⟨4313166295116658793769757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5750888393488878391693009 4313166295116658793769757)
                    ·
                      refine ⟨1617437360668747047663659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4313166295116658793769757 1617437360668747047663659)
                      ·
                        rfl

theorem cell23_3149948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_3149948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149948 prefixEnd_3149948 := by exact prefixLift 3149948
  have htrace : WordTrace (prefixWord ++ tailWord_3149948) baseStart_3149948 baseEnd_3149948 := by
    simpa [prefixWord, tailWord_3149948, baseEnd_3149948] using wordTrace_append hprefix tailTrace_3149948
  have hstable : (prefixWord ++ tailWord_3149948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149948).length < 2 ^ (prefixWord ++ tailWord_3149948).sum := by decide
  have hdescent : baseEnd_3149948 < baseStart_3149948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149961 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 5, 1, 3]
def baseStart_3149961 : Nat := 118140960795 + 3149961 * 2 ^ 59
def prefixEnd_3149961 : Nat := 4983230072969 + 3 ^ 40 * 3149961 * 2
def baseEnd_3149961 : Nat := 1617444035917255496801099

theorem tailTrace_3149961 : CollatzResearch.WordTrace tailWord_3149961 prefixEnd_3149961 1617444035917255496801099 := by
  unfold tailWord_3149961
  simp only [CollatzResearch.WordTrace]
  refine ⟨114888516141236742353889737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76592344094157828235926491 114888516141236742353889737)
  ·
    refine ⟨86166387105927556765417303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114888516141236742353889737 86166387105927556765417303)
    ·
      refine ⟨129249580658891335148125955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86166387105927556765417303 129249580658891335148125955)
      ·
        refine ⟨193874370988337002722188933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129249580658891335148125955 193874370988337002722188933)
        ·
          refine ⟨36351444560313188010410425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193874370988337002722188933 36351444560313188010410425)
          ·
            refine ⟨27263583420234891007807819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36351444560313188010410425 27263583420234891007807819)
            ·
              refine ⟨40895375130352336511711729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27263583420234891007807819 40895375130352336511711729)
              ·
                refine ⟨30671531347764252383783797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40895375130352336511711729 30671531347764252383783797)
                ·
                  refine ⟨2875456063852898660979731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30671531347764252383783797 2875456063852898660979731)
                  ·
                    refine ⟨4313184095779347991469597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2875456063852898660979731 4313184095779347991469597)
                    ·
                      refine ⟨1617444035917255496801099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4313184095779347991469597 1617444035917255496801099)
                      ·
                        rfl

theorem cell23_3149961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 5, 1, 3].length) (baseStart_3149961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149961 prefixEnd_3149961 := by exact prefixLift 3149961
  have htrace : WordTrace (prefixWord ++ tailWord_3149961) baseStart_3149961 baseEnd_3149961 := by
    simpa [prefixWord, tailWord_3149961, baseEnd_3149961] using wordTrace_append hprefix tailTrace_3149961
  have hstable : (prefixWord ++ tailWord_3149961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149961).length < 2 ^ (prefixWord ++ tailWord_3149961).sum := by decide
  have hdescent : baseEnd_3149961 < baseStart_3149961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3149971 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 4, 3, 2]
def baseStart_3149971 : Nat := 118140960795 + 3149971 * 2 ^ 59
def prefixEnd_3149971 : Nat := 4983230072969 + 3 ^ 40 * 3149971 * 2
def baseEnd_3149971 : Nat := 1617449170723800457676053

theorem tailTrace_3149971 : CollatzResearch.WordTrace tailWord_3149971 prefixEnd_3149971 1617449170723800457676053 := by
  unfold tailWord_3149971
  simp only [CollatzResearch.WordTrace]
  refine ⟨114888880871200514061753767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76592587247467009374502511 114888880871200514061753767)
  ·
    refine ⟨172333321306800771092630651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114888880871200514061753767 172333321306800771092630651)
    ·
      refine ⟨258499981960201156638945977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172333321306800771092630651 258499981960201156638945977)
      ·
        refine ⟨193874986470150867479209483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258499981960201156638945977 193874986470150867479209483)
        ·
          refine ⟨290812479705226301218814225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193874986470150867479209483 290812479705226301218814225)
          ·
            refine ⟨218109359778919725914110669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290812479705226301218814225 218109359778919725914110669)
            ·
              refine ⟨81791009917094897217791501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 218109359778919725914110669 81791009917094897217791501)
              ·
                refine ⟨30671628718910586456671813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81791009917094897217791501 30671628718910586456671813)
                ·
                  refine ⟨5750930384795734960625965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30671628718910586456671813 5750930384795734960625965)
                  ·
                    refine ⟨2156598894298400610234737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5750930384795734960625965 2156598894298400610234737)
                    ·
                      refine ⟨1617449170723800457676053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2156598894298400610234737 1617449170723800457676053)
                      ·
                        rfl

theorem cell23_3149971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 3, 2].length) (baseStart_3149971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3149971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3149971 prefixEnd_3149971 := by exact prefixLift 3149971
  have htrace : WordTrace (prefixWord ++ tailWord_3149971) baseStart_3149971 baseEnd_3149971 := by
    simpa [prefixWord, tailWord_3149971, baseEnd_3149971] using wordTrace_append hprefix tailTrace_3149971
  have hstable : (prefixWord ++ tailWord_3149971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3149971).length < 2 ^ (prefixWord ++ tailWord_3149971).sum := by decide
  have hdescent : baseEnd_3149971 < baseStart_3149971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3149971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150045 : List Nat := [1, 4, 3, 2, 1, 2, 1, 3, 2, 4]
def baseStart_3150045 : Nat := 118140960795 + 3150045 * 2 ^ 59
def prefixEnd_3150045 : Nat := 4983230072969 + 3 ^ 40 * 3150045 * 2
def baseEnd_3150045 : Nat := 539162389430744389383571

theorem tailTrace_3150045 : CollatzResearch.WordTrace tailWord_3150045 prefixEnd_3150045 539162389430744389383571 := by
  unfold tailWord_3150045
  simp only [CollatzResearch.WordTrace]
  refine ⟨114891579872932424699947589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76594386581954949799965059 114891579872932424699947589)
  ·
    refine ⟨21542171226174829631240173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114891579872932424699947589 21542171226174829631240173)
    ·
      refine ⟨8078314209815561111715065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21542171226174829631240173 8078314209815561111715065)
      ·
        refine ⟨6058735657361670833786299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8078314209815561111715065 6058735657361670833786299)
        ·
          refine ⟨9088103486042506250679449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6058735657361670833786299 9088103486042506250679449)
          ·
            refine ⟨6816077614531879688009587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9088103486042506250679449 6816077614531879688009587)
            ·
              refine ⟨10224116421797819532014381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6816077614531879688009587 10224116421797819532014381)
              ·
                refine ⟨3834043658174182324505393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10224116421797819532014381 3834043658174182324505393)
                ·
                  refine ⟨2875532743630636743379045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3834043658174182324505393 2875532743630636743379045)
                  ·
                    refine ⟨539162389430744389383571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2875532743630636743379045 539162389430744389383571)
                    ·
                      rfl

theorem cell23_3150045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_3150045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150045 prefixEnd_3150045 := by exact prefixLift 3150045
  have htrace : WordTrace (prefixWord ++ tailWord_3150045) baseStart_3150045 baseEnd_3150045 := by
    simpa [prefixWord, tailWord_3150045, baseEnd_3150045] using wordTrace_append hprefix tailTrace_3150045
  have hstable : (prefixWord ++ tailWord_3150045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150045).length < 2 ^ (prefixWord ++ tailWord_3150045).sum := by decide
  have hdescent : baseEnd_3150045 < baseStart_3150045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150055 : List Nat := [1, 1, 5, 3, 1, 1, 3, 2, 1, 2, 3]
def baseStart_3150055 : Nat := 118140960795 + 3150055 * 2 ^ 59
def prefixEnd_3150055 : Nat := 4983230072969 + 3 ^ 40 * 3150055 * 2
def baseEnd_3150055 : Nat := 1617492303098778129025667

theorem tailTrace_3150055 : CollatzResearch.WordTrace tailWord_3150055 prefixEnd_3150055 1617492303098778129025667 := by
  unfold tailWord_3150055
  simp only [CollatzResearch.WordTrace]
  refine ⟨114891944602896196407811619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76594629735264130938541079 114891944602896196407811619)
  ·
    refine ⟨172337916904344294611717429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114891944602896196407811619 172337916904344294611717429)
    ·
      refine ⟨16156679709782277619848509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 172337916904344294611717429 16156679709782277619848509)
      ·
        refine ⟨6058754891168354107443191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16156679709782277619848509 6058754891168354107443191)
        ·
          refine ⟨9088132336752531161164787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6058754891168354107443191 9088132336752531161164787)
          ·
            refine ⟨13632198505128796741747181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9088132336752531161164787 13632198505128796741747181)
            ·
              refine ⟨5112074439423298778155193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13632198505128796741747181 5112074439423298778155193)
              ·
                refine ⟨3834055829567474083616395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5112074439423298778155193 3834055829567474083616395)
                ·
                  refine ⟨5751083744351211125424593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3834055829567474083616395 5751083744351211125424593)
                  ·
                    refine ⟨4313312808263408344068445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5751083744351211125424593 4313312808263408344068445)
                    ·
                      refine ⟨1617492303098778129025667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4313312808263408344068445 1617492303098778129025667)
                      ·
                        rfl

theorem cell23_3150055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_3150055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150055 prefixEnd_3150055 := by exact prefixLift 3150055
  have htrace : WordTrace (prefixWord ++ tailWord_3150055) baseStart_3150055 baseEnd_3150055 := by
    simpa [prefixWord, tailWord_3150055, baseEnd_3150055] using wordTrace_append hprefix tailTrace_3150055
  have hstable : (prefixWord ++ tailWord_3150055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150055).length < 2 ^ (prefixWord ++ tailWord_3150055).sum := by decide
  have hdescent : baseEnd_3150055 < baseStart_3150055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150064 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 5]
def baseStart_3150064 : Nat := 118140960795 + 3150064 * 2 ^ 59
def prefixEnd_3150064 : Nat := 4983230072969 + 3 ^ 40 * 3150064 * 2
def baseEnd_3150064 : Nat := 1617496924424668593813125

theorem tailTrace_3150064 : CollatzResearch.WordTrace tailWord_3150064 prefixEnd_3150064 1617496924424668593813125 := by
  unfold tailWord_3150064
  simp only [CollatzResearch.WordTrace]
  refine ⟨57446136429931795472444623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76594848573242393963259497 57446136429931795472444623)
  ·
    refine ⟨86169204644897693208666935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57446136429931795472444623 86169204644897693208666935)
    ·
      refine ⟨129253806967346539813000403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86169204644897693208666935 129253806967346539813000403)
      ·
        refine ⟨193880710451019809719500605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129253806967346539813000403 193880710451019809719500605)
        ·
          refine ⟨72705266419132428644812727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193880710451019809719500605 72705266419132428644812727)
          ·
            refine ⟨109057899628698642967219091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72705266419132428644812727 109057899628698642967219091)
            ·
              refine ⟨163586849443047964450828637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109057899628698642967219091 163586849443047964450828637)
              ·
                refine ⟨61345068541142986669060739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163586849443047964450828637 61345068541142986669060739)
                ·
                  refine ⟨92017602811714480003591109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61345068541142986669060739 92017602811714480003591109)
                  ·
                    refine ⟨17253300527196465000673333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92017602811714480003591109 17253300527196465000673333)
                    ·
                      refine ⟨1617496924424668593813125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17253300527196465000673333 1617496924424668593813125)
                      ·
                        rfl

theorem cell23_3150064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 5].length) (baseStart_3150064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150064 prefixEnd_3150064 := by exact prefixLift 3150064
  have htrace : WordTrace (prefixWord ++ tailWord_3150064) baseStart_3150064 baseEnd_3150064 := by
    simpa [prefixWord, tailWord_3150064, baseEnd_3150064] using wordTrace_append hprefix tailTrace_3150064
  have hstable : (prefixWord ++ tailWord_3150064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150064).length < 2 ^ (prefixWord ++ tailWord_3150064).sum := by decide
  have hdescent : baseEnd_3150064 < baseStart_3150064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150129 : List Nat := [1, 2, 2, 3, 4, 2, 2, 1, 1, 3, 2]
def baseStart_3150129 : Nat := 118140960795 + 3150129 * 2 ^ 59
def prefixEnd_3150129 : Nat := 4983230072969 + 3 ^ 40 * 3150129 * 2
def baseEnd_3150129 : Nat := 1617530300667210839500327

theorem tailTrace_3150129 : CollatzResearch.WordTrace tailWord_3150129 prefixEnd_3150129 1617530300667210839500327 := by
  unfold tailWord_3150129
  simp only [CollatzResearch.WordTrace]
  refine ⟨114894643604628107046005441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76596429069752071364003627 114894643604628107046005441)
  ·
    refine ⟨86170982703471080284504081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114894643604628107046005441 86170982703471080284504081)
    ·
      refine ⟨64628237027603310213378061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86170982703471080284504081 64628237027603310213378061)
      ·
        refine ⟨24235588885351241330016773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64628237027603310213378061 24235588885351241330016773)
        ·
          refine ⟨4544172916003357749378145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24235588885351241330016773 4544172916003357749378145)
          ·
            refine ⟨3408129687002518312033609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4544172916003357749378145 3408129687002518312033609)
            ·
              refine ⟨2556097265251888734025207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3408129687002518312033609 2556097265251888734025207)
              ·
                refine ⟨3834145897877833101037811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2556097265251888734025207 3834145897877833101037811)
                ·
                  refine ⟨5751218846816749651556717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3834145897877833101037811 5751218846816749651556717)
                  ·
                    refine ⟨2156707067556281119333769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5751218846816749651556717 2156707067556281119333769)
                    ·
                      refine ⟨1617530300667210839500327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2156707067556281119333769 1617530300667210839500327)
                      ·
                        rfl

theorem cell23_3150129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_3150129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150129 prefixEnd_3150129 := by exact prefixLift 3150129
  have htrace : WordTrace (prefixWord ++ tailWord_3150129) baseStart_3150129 baseEnd_3150129 := by
    simpa [prefixWord, tailWord_3150129, baseEnd_3150129] using wordTrace_append hprefix tailTrace_3150129
  have hstable : (prefixWord ++ tailWord_3150129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150129).length < 2 ^ (prefixWord ++ tailWord_3150129).sum := by decide
  have hdescent : baseEnd_3150129 < baseStart_3150129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150142 : List Nat := [4, 2, 1, 2, 1, 3, 1, 1, 4, 2, 2]
def baseStart_3150142 : Nat := 118140960795 + 3150142 * 2 ^ 59
def prefixEnd_3150142 : Nat := 4983230072969 + 3 ^ 40 * 3150142 * 2
def baseEnd_3150142 : Nat := 1617536975915719288637767

theorem tailTrace_3150142 : CollatzResearch.WordTrace tailWord_3150142 prefixEnd_3150142 1617536975915719288637767 := by
  unfold tailWord_3150142
  simp only [CollatzResearch.WordTrace]
  refine ⟨14361889719197626283278585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76596745169054006844152453 14361889719197626283278585)
  ·
    refine ⟨10771417289398219712458939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14361889719197626283278585 10771417289398219712458939)
    ·
      refine ⟨16157125934097329568688409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10771417289398219712458939 16157125934097329568688409)
      ·
        refine ⟨12117844450572997176516307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16157125934097329568688409 12117844450572997176516307)
        ·
          refine ⟨18176766675859495764774461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12117844450572997176516307 18176766675859495764774461)
          ·
            refine ⟨6816287503447310911790423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18176766675859495764774461 6816287503447310911790423)
            ·
              refine ⟨10224431255170966367685635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6816287503447310911790423 10224431255170966367685635)
              ·
                refine ⟨15336646882756449551528453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10224431255170966367685635 15336646882756449551528453)
                ·
                  refine ⟨2875621290516834290911585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15336646882756449551528453 2875621290516834290911585)
                  ·
                    refine ⟨2156715967887625718183689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2875621290516834290911585 2156715967887625718183689)
                    ·
                      refine ⟨1617536975915719288637767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2156715967887625718183689 1617536975915719288637767)
                      ·
                        rfl

theorem cell23_3150142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_3150142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150142 prefixEnd_3150142 := by exact prefixLift 3150142
  have htrace : WordTrace (prefixWord ++ tailWord_3150142) baseStart_3150142 baseEnd_3150142 := by
    simpa [prefixWord, tailWord_3150142, baseEnd_3150142] using wordTrace_append hprefix tailTrace_3150142
  have hstable : (prefixWord ++ tailWord_3150142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150142).length < 2 ^ (prefixWord ++ tailWord_3150142).sum := by decide
  have hdescent : baseEnd_3150142 < baseStart_3150142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150161 : List Nat := [1, 2, 2, 1, 4, 2, 1, 2, 1, 7]
def baseStart_3150161 : Nat := 118140960795 + 3150161 * 2 ^ 59
def prefixEnd_3150161 : Nat := 4983230072969 + 3 ^ 40 * 3150161 * 2
def baseEnd_3150161 : Nat := 539182244016051571433393

theorem tailTrace_3150161 : CollatzResearch.WordTrace tailWord_3150161 prefixEnd_3150161 539182244016051571433393 := by
  unfold tailWord_3150161
  simp only [CollatzResearch.WordTrace]
  refine ⟨114895810740512176511170337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76597207160341451007446891 114895810740512176511170337)
  ·
    refine ⟨86171858055384132383377753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114895810740512176511170337 86171858055384132383377753)
    ·
      refine ⟨64628893541538099287533315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86171858055384132383377753 64628893541538099287533315)
      ·
        refine ⟨96943340312307148931299973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64628893541538099287533315 96943340312307148931299973)
        ·
          refine ⟨18176876308557590424618745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96943340312307148931299973 18176876308557590424618745)
          ·
            refine ⟨13632657231418192818464059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18176876308557590424618745 13632657231418192818464059)
            ·
              refine ⟨20448985847127289227696089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13632657231418192818464059 20448985847127289227696089)
              ·
                refine ⟨15336739385345466920772067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20448985847127289227696089 15336739385345466920772067)
                ·
                  refine ⟨23005109078018200381158101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15336739385345466920772067 23005109078018200381158101)
                  ·
                    refine ⟨539182244016051571433393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23005109078018200381158101 539182244016051571433393)
                    ·
                      rfl

theorem cell23_3150161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 7].length) (baseStart_3150161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150161 prefixEnd_3150161 := by exact prefixLift 3150161
  have htrace : WordTrace (prefixWord ++ tailWord_3150161) baseStart_3150161 baseEnd_3150161 := by
    simpa [prefixWord, tailWord_3150161, baseEnd_3150161] using wordTrace_append hprefix tailTrace_3150161
  have hstable : (prefixWord ++ tailWord_3150161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150161).length < 2 ^ (prefixWord ++ tailWord_3150161).sum := by decide
  have hdescent : baseEnd_3150161 < baseStart_3150161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150178 : List Nat := [3, 3, 2, 1, 1, 2, 2, 1, 1, 7]
def baseStart_3150178 : Nat := 118140960795 + 3150178 * 2 ^ 59
def prefixEnd_3150178 : Nat := 4983230072969 + 3 ^ 40 * 3150178 * 2
def baseEnd_3150178 : Nat := 539185153739760382595867

theorem tailTrace_3150178 : CollatzResearch.WordTrace tailWord_3150178 prefixEnd_3150178 539185153739760382595867 := by
  unfold tailWord_3150178
  simp only [CollatzResearch.WordTrace]
  refine ⟨28724107695362647103634797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76597620520967058943026125 28724107695362647103634797)
  ·
    refine ⟨10771540385760992663863049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28724107695362647103634797 10771540385760992663863049)
    ·
      refine ⟨8078655289320744497897287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10771540385760992663863049 8078655289320744497897287)
      ·
        refine ⟨12117982933981116746845931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8078655289320744497897287 12117982933981116746845931)
        ·
          refine ⟨18176974400971675120268897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12117982933981116746845931 18176974400971675120268897)
          ·
            refine ⟨13632730800728756340201673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18176974400971675120268897 13632730800728756340201673)
            ·
              refine ⟨10224548100546567255151255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13632730800728756340201673 10224548100546567255151255)
              ·
                refine ⟨15336822150819850882726883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10224548100546567255151255 15336822150819850882726883)
                ·
                  refine ⟨23005233226229776324090325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15336822150819850882726883 23005233226229776324090325)
                  ·
                    refine ⟨539185153739760382595867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23005233226229776324090325 539185153739760382595867)
                    ·
                      rfl

theorem cell23_3150178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_3150178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150178 prefixEnd_3150178 := by exact prefixLift 3150178
  have htrace : WordTrace (prefixWord ++ tailWord_3150178) baseStart_3150178 baseEnd_3150178 := by
    simpa [prefixWord, tailWord_3150178, baseEnd_3150178] using wordTrace_append hprefix tailTrace_3150178
  have hstable : (prefixWord ++ tailWord_3150178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150178).length < 2 ^ (prefixWord ++ tailWord_3150178).sum := by decide
  have hdescent : baseEnd_3150178 < baseStart_3150178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150210 : List Nat := [3, 4, 2, 1, 3, 1, 2, 1, 2, 2, 2]
def baseStart_3150210 : Nat := 118140960795 + 3150210 * 2 ^ 59
def prefixEnd_3150210 : Nat := 4983230072969 + 3 ^ 40 * 3150210 * 2
def baseEnd_3150210 : Nat := 1617571892600225022587455

theorem tailTrace_3150210 : CollatzResearch.WordTrace tailWord_3150210 prefixEnd_3150210 1617571892600225022587455 := by
  unfold tailWord_3150210
  simp only [CollatzResearch.WordTrace]
  refine ⟨28724399479333664469926021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76598398611556438586469389 28724399479333664469926021)
  ·
    refine ⟨5385824902375062088111129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28724399479333664469926021 5385824902375062088111129)
    ·
      refine ⟨4039368676781296566083347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5385824902375062088111129 4039368676781296566083347)
      ·
        refine ⟨6059053015171944849125021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4039368676781296566083347 6059053015171944849125021)
        ·
          refine ⟨2272144880689479318421883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6059053015171944849125021 2272144880689479318421883)
          ·
            refine ⟨3408217321034218977632825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2272144880689479318421883 3408217321034218977632825)
            ·
              refine ⟨2556162990775664233224619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3408217321034218977632825 2556162990775664233224619)
              ·
                refine ⟨3834244486163496349836929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2556162990775664233224619 3834244486163496349836929)
                ·
                  refine ⟨2875683364622622262377697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3834244486163496349836929 2875683364622622262377697)
                  ·
                    refine ⟨2156762523466966696783273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2875683364622622262377697 2156762523466966696783273)
                    ·
                      refine ⟨1617571892600225022587455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2156762523466966696783273 1617571892600225022587455)
                      ·
                        rfl

theorem cell23_3150210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_3150210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150210 prefixEnd_3150210 := by exact prefixLift 3150210
  have htrace : WordTrace (prefixWord ++ tailWord_3150210) baseStart_3150210 baseEnd_3150210 := by
    simpa [prefixWord, tailWord_3150210, baseEnd_3150210] using wordTrace_append hprefix tailTrace_3150210
  have hstable : (prefixWord ++ tailWord_3150210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150210).length < 2 ^ (prefixWord ++ tailWord_3150210).sum := by decide
  have hdescent : baseEnd_3150210 < baseStart_3150210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150242 : List Nat := [3, 3, 1, 2, 1, 1, 2, 5, 1, 4]
def baseStart_3150242 : Nat := 118140960795 + 3150242 * 2 ^ 59
def prefixEnd_3150242 : Nat := 4983230072969 + 3 ^ 40 * 3150242 * 2
def baseEnd_3150242 : Nat := 539196107993722965795769

theorem tailTrace_3150242 : CollatzResearch.WordTrace tailWord_3150242 prefixEnd_3150242 539196107993722965795769 := by
  unfold tailWord_3150242
  simp only [CollatzResearch.WordTrace]
  refine ⟨28724691263304681836217245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76599176702145818229912653 28724691263304681836217245)
  ·
    refine ⟨10771759223739255688581467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28724691263304681836217245 10771759223739255688581467)
    ·
      refine ⟨16157638835608883532872201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10771759223739255688581467 16157638835608883532872201)
      ·
        refine ⟨12118229126706662649654151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16157638835608883532872201 12118229126706662649654151)
        ·
          refine ⟨18177343690059993974481227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12118229126706662649654151 18177343690059993974481227)
          ·
            refine ⟨27266015535089990961721841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18177343690059993974481227 27266015535089990961721841)
            ·
              refine ⟨20449511651317493221291381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27266015535089990961721841 20449511651317493221291381)
              ·
                refine ⟨1917141717311014989496067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20449511651317493221291381 1917141717311014989496067)
                ·
                  refine ⟨2875712575966522484244101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1917141717311014989496067 2875712575966522484244101)
                  ·
                    refine ⟨539196107993722965795769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2875712575966522484244101 539196107993722965795769)
                    ·
                      rfl

theorem cell23_3150242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_3150242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150242 prefixEnd_3150242 := by exact prefixLift 3150242
  have htrace : WordTrace (prefixWord ++ tailWord_3150242) baseStart_3150242 baseEnd_3150242 := by
    simpa [prefixWord, tailWord_3150242, baseEnd_3150242] using wordTrace_append hprefix tailTrace_3150242
  have hstable : (prefixWord ++ tailWord_3150242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150242).length < 2 ^ (prefixWord ++ tailWord_3150242).sum := by decide
  have hdescent : baseEnd_3150242 < baseStart_3150242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150292 : List Nat := [2, 4, 1, 2, 2, 2, 1, 1, 1, 5, 2]
def baseStart_3150292 : Nat := 118140960795 + 3150292 * 2 ^ 59
def prefixEnd_3150292 : Nat := 4983230072969 + 3 ^ 40 * 3150292 * 2
def baseEnd_3150292 : Nat := 1617613998013893701762077

theorem tailTrace_3150292 : CollatzResearch.WordTrace tailWord_3150292 prefixEnd_3150292 1617613998013893701762077 := by
  unfold tailWord_3150292
  simp only [CollatzResearch.WordTrace]
  refine ⟨57450294351518792942094565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76600392468691723922792753 57450294351518792942094565)
  ·
    refine ⟨10771930190909773676642731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57450294351518792942094565 10771930190909773676642731)
    ·
      refine ⟨16157895286364660514964097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10771930190909773676642731 16157895286364660514964097)
      ·
        refine ⟨12118421464773495386223073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16157895286364660514964097 12118421464773495386223073)
        ·
          refine ⟨9088816098580121539667305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12118421464773495386223073 9088816098580121539667305)
          ·
            refine ⟨6816612073935091154750479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9088816098580121539667305 6816612073935091154750479)
            ·
              refine ⟨10224918110902636732125719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6816612073935091154750479 10224918110902636732125719)
              ·
                refine ⟨15337377166353955098188579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10224918110902636732125719 15337377166353955098188579)
                ·
                  refine ⟨23006065749530932647282869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15337377166353955098188579 23006065749530932647282869)
                  ·
                    refine ⟨2156818664018524935682769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23006065749530932647282869 2156818664018524935682769)
                    ·
                      refine ⟨1617613998013893701762077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2156818664018524935682769 1617613998013893701762077)
                      ·
                        rfl

theorem cell23_3150292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_3150292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150292 prefixEnd_3150292 := by exact prefixLift 3150292
  have htrace : WordTrace (prefixWord ++ tailWord_3150292) baseStart_3150292 baseEnd_3150292 := by
    simpa [prefixWord, tailWord_3150292, baseEnd_3150292] using wordTrace_append hprefix tailTrace_3150292
  have hstable : (prefixWord ++ tailWord_3150292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150292).length < 2 ^ (prefixWord ++ tailWord_3150292).sum := by decide
  have hdescent : baseEnd_3150292 < baseStart_3150292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150298 : List Nat := [3, 1, 1, 2, 3, 1, 1, 4, 1, 6]
def baseStart_3150298 : Nat := 118140960795 + 3150298 * 2 ^ 59
def prefixEnd_3150298 : Nat := 4983230072969 + 3 ^ 40 * 3150298 * 2
def baseEnd_3150298 : Nat := 539205692965940226095683

theorem tailTrace_3150298 : CollatzResearch.WordTrace tailWord_3150298 prefixEnd_3150298 539205692965940226095683 := by
  unfold tailWord_3150298
  simp only [CollatzResearch.WordTrace]
  refine ⟨28725201885253962227226887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76600538360677232605938365 28725201885253962227226887)
  ·
    refine ⟨43087802827880943340840331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28725201885253962227226887 43087802827880943340840331)
    ·
      refine ⟨64631704241821415011260497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43087802827880943340840331 64631704241821415011260497)
      ·
        refine ⟨48473778181366061258445373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64631704241821415011260497 48473778181366061258445373)
        ·
          refine ⟨18177666818012272971917015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48473778181366061258445373 18177666818012272971917015)
          ·
            refine ⟨27266500227018409457875523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18177666818012272971917015 27266500227018409457875523)
            ·
              refine ⟨40899750340527614186813285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27266500227018409457875523 40899750340527614186813285)
              ·
                refine ⟨7668703188848927660027491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40899750340527614186813285 7668703188848927660027491)
                ·
                  refine ⟨11503054783273391490041237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7668703188848927660027491 11503054783273391490041237)
                  ·
                    refine ⟨539205692965940226095683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11503054783273391490041237 539205692965940226095683)
                    ·
                      rfl

theorem cell23_3150298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 1, 6].length) (baseStart_3150298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150298 prefixEnd_3150298 := by exact prefixLift 3150298
  have htrace : WordTrace (prefixWord ++ tailWord_3150298) baseStart_3150298 baseEnd_3150298 := by
    simpa [prefixWord, tailWord_3150298, baseEnd_3150298] using wordTrace_append hprefix tailTrace_3150298
  have hstable : (prefixWord ++ tailWord_3150298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150298).length < 2 ^ (prefixWord ++ tailWord_3150298).sum := by decide
  have hdescent : baseEnd_3150298 < baseStart_3150298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150305 : List Nat := [1, 2, 3, 1, 2, 2, 3, 3, 1, 1, 4]
def baseStart_3150305 : Nat := 118140960795 + 3150305 * 2 ^ 59
def prefixEnd_3150305 : Nat := 4983230072969 + 3 ^ 40 * 3150305 * 2
def baseEnd_3150305 : Nat := 1617620673262402150899517

theorem tailTrace_3150305 : CollatzResearch.WordTrace tailWord_3150305 prefixEnd_3150305 1617620673262402150899517 := by
  unfold tailWord_3150305
  simp only [CollatzResearch.WordTrace]
  refine ⟨114901062851990489104412369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76600708567993659402941579 114901062851990489104412369)
  ·
    refine ⟨86175797138992866828309277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114901062851990489104412369 86175797138992866828309277)
    ·
      refine ⟨32315923927122325060615979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86175797138992866828309277 32315923927122325060615979)
      ·
        refine ⟨48473885890683487590923969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32315923927122325060615979 48473885890683487590923969)
        ·
          refine ⟨36355414418012615693192977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48473885890683487590923969 36355414418012615693192977)
          ·
            refine ⟨27266560813509461769894733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36355414418012615693192977 27266560813509461769894733)
            ·
              refine ⟨10224960305066048163710525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27266560813509461769894733 10224960305066048163710525)
              ·
                refine ⟨3834360114399768061391447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10224960305066048163710525 3834360114399768061391447)
                ·
                  refine ⟨5751540171599652092087171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3834360114399768061391447 5751540171599652092087171)
                  ·
                    refine ⟨8627310257399478138130757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5751540171599652092087171 8627310257399478138130757)
                    ·
                      refine ⟨1617620673262402150899517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8627310257399478138130757 1617620673262402150899517)
                      ·
                        rfl

theorem cell23_3150305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_3150305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150305 prefixEnd_3150305 := by exact prefixLift 3150305
  have htrace : WordTrace (prefixWord ++ tailWord_3150305) baseStart_3150305 baseEnd_3150305 := by
    simpa [prefixWord, tailWord_3150305, baseEnd_3150305] using wordTrace_append hprefix tailTrace_3150305
  have hstable : (prefixWord ++ tailWord_3150305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150305).length < 2 ^ (prefixWord ++ tailWord_3150305).sum := by decide
  have hdescent : baseEnd_3150305 < baseStart_3150305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150306 : List Nat := [3, 3, 3, 2, 2, 1, 1, 2, 6]
def baseStart_3150306 : Nat := 118140960795 + 3150306 * 2 ^ 59
def prefixEnd_3150306 : Nat := 4983230072969 + 3 ^ 40 * 3150306 * 2
def baseEnd_3150306 : Nat := 179735687415895182998557

theorem tailTrace_3150306 : CollatzResearch.WordTrace tailWord_3150306 prefixEnd_3150306 179735687415895182998557 := by
  unfold tailWord_3150306
  simp only [CollatzResearch.WordTrace]
  refine ⟨28725274831246716568799693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76600732883324577516799181 28725274831246716568799693)
  ·
    refine ⟨10771978061717518713299885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28725274831246716568799693 10771978061717518713299885)
    ·
      refine ⟨4039491773144069517487457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10771978061717518713299885 4039491773144069517487457)
      ·
        refine ⟨3029618829858052138115593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4039491773144069517487457 3029618829858052138115593)
        ·
          refine ⟨2272214122393539103586695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3029618829858052138115593 2272214122393539103586695)
          ·
            refine ⟨3408321183590308655380043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2272214122393539103586695 3408321183590308655380043)
            ·
              refine ⟨5112481775385462983070065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3408321183590308655380043 5112481775385462983070065)
              ·
                refine ⟨3834361331539097237302549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5112481775385462983070065 3834361331539097237302549)
                ·
                  refine ⟨179735687415895182998557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3834361331539097237302549 179735687415895182998557)
                  ·
                    rfl

theorem cell23_3150306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_3150306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150306 prefixEnd_3150306 := by exact prefixLift 3150306
  have htrace : WordTrace (prefixWord ++ tailWord_3150306) baseStart_3150306 baseEnd_3150306 := by
    simpa [prefixWord, tailWord_3150306, baseEnd_3150306] using wordTrace_append hprefix tailTrace_3150306
  have hstable : (prefixWord ++ tailWord_3150306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150306).length < 2 ^ (prefixWord ++ tailWord_3150306).sum := by decide
  have hdescent : baseEnd_3150306 < baseStart_3150306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150349 : List Nat := [1, 7, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_3150349 : Nat := 118140960795 + 3150349 * 2 ^ 59
def prefixEnd_3150349 : Nat := 4983230072969 + 3 ^ 40 * 3150349 * 2
def baseEnd_3150349 : Nat := 539214422137066659583105

theorem tailTrace_3150349 : CollatzResearch.WordTrace tailWord_3150349 prefixEnd_3150349 539214422137066659583105 := by
  unfold tailWord_3150349
  simp only [CollatzResearch.WordTrace]
  refine ⟨114902667663831084619014101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76601778442554056412676067 114902667663831084619014101)
  ·
    refine ⟨2693031273371041045758143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 114902667663831084619014101 2693031273371041045758143)
    ·
      refine ⟨4039546910056561568637215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2693031273371041045758143 4039546910056561568637215)
      ·
        refine ⟨6059320365084842352955823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4039546910056561568637215 6059320365084842352955823)
        ·
          refine ⟨9088980547627263529433735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6059320365084842352955823 9088980547627263529433735)
          ·
            refine ⟨13633470821440895294150603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9088980547627263529433735 13633470821440895294150603)
            ·
              refine ⟨20450206232161342941225905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13633470821440895294150603 20450206232161342941225905)
              ·
                refine ⟨15337654674121007205919429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20450206232161342941225905 15337654674121007205919429)
                ·
                  refine ⟨2875810251397688851109893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15337654674121007205919429 2875810251397688851109893)
                  ·
                    refine ⟨539214422137066659583105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2875810251397688851109893 539214422137066659583105)
                    ·
                      rfl

theorem cell23_3150349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_3150349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150349 prefixEnd_3150349 := by exact prefixLift 3150349
  have htrace : WordTrace (prefixWord ++ tailWord_3150349) baseStart_3150349 baseEnd_3150349 := by
    simpa [prefixWord, tailWord_3150349, baseEnd_3150349] using wordTrace_append hprefix tailTrace_3150349
  have hstable : (prefixWord ++ tailWord_3150349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150349).length < 2 ^ (prefixWord ++ tailWord_3150349).sum := by decide
  have hdescent : baseEnd_3150349 < baseStart_3150349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150355 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 6, 1, 3]
def baseStart_3150355 : Nat := 118140960795 + 3150355 * 2 ^ 59
def prefixEnd_3150355 : Nat := 4983230072969 + 3 ^ 40 * 3150355 * 2
def baseEnd_3150355 : Nat := 1617646347295126955274287

theorem tailTrace_3150355 : CollatzResearch.WordTrace tailWord_3150355 prefixEnd_3150355 1617646347295126955274287 := by
  unfold tailWord_3150355
  simp only [CollatzResearch.WordTrace]
  refine ⟨114902886501809347643732519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76601924334539565095821679 114902886501809347643732519)
  ·
    refine ⟨172354329752714021465598779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114902886501809347643732519 172354329752714021465598779)
    ·
      refine ⟨258531494629071032198398169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172354329752714021465598779 258531494629071032198398169)
      ·
        refine ⟨193898620971803274148798627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258531494629071032198398169 193898620971803274148798627)
        ·
          refine ⟨290847931457704911223197941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193898620971803274148798627 290847931457704911223197941)
          ·
            refine ⟨27266993574159835427174807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 290847931457704911223197941 27266993574159835427174807)
            ·
              refine ⟨40900490361239753140762211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27266993574159835427174807 40900490361239753140762211)
              ·
                refine ⟨61350735541859629711143317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40900490361239753140762211 61350735541859629711143317)
                ·
                  refine ⟨2875815728524670142709843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61350735541859629711143317 2875815728524670142709843)
                  ·
                    refine ⟨4313723592787005214064765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2875815728524670142709843 4313723592787005214064765)
                    ·
                      refine ⟨1617646347295126955274287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4313723592787005214064765 1617646347295126955274287)
                      ·
                        rfl

theorem cell23_3150355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 6, 1, 3].length) (baseStart_3150355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150355 prefixEnd_3150355 := by exact prefixLift 3150355
  have htrace : WordTrace (prefixWord ++ tailWord_3150355) baseStart_3150355 baseEnd_3150355 := by
    simpa [prefixWord, tailWord_3150355, baseEnd_3150355] using wordTrace_append hprefix tailTrace_3150355
  have hstable : (prefixWord ++ tailWord_3150355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150355).length < 2 ^ (prefixWord ++ tailWord_3150355).sum := by decide
  have hdescent : baseEnd_3150355 < baseStart_3150355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150412 : List Nat := [2, 2, 1, 3, 1, 2, 3, 2, 1, 4, 2]
def baseStart_3150412 : Nat := 118140960795 + 3150412 * 2 ^ 59
def prefixEnd_3150412 : Nat := 4983230072969 + 3 ^ 40 * 3150412 * 2
def baseEnd_3150412 : Nat := 1617675615692433232261525

theorem tailTrace_3150412 : CollatzResearch.WordTrace tailWord_3150412 prefixEnd_3150412 1617675615692433232261525 := by
  unfold tailWord_3150412
  simp only [CollatzResearch.WordTrace]
  refine ⟨57452482731301423189278745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76603310308401897585704993 57452482731301423189278745)
  ·
    refine ⟨43089362048476067391959059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57452482731301423189278745 43089362048476067391959059)
    ·
      refine ⟨64634043072714101087938589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43089362048476067391959059 64634043072714101087938589)
      ·
        refine ⟨24237766152267787907976971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64634043072714101087938589 24237766152267787907976971)
        ·
          refine ⟨36356649228401681861965457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24237766152267787907976971 36356649228401681861965457)
          ·
            refine ⟨27267486921301261396474093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36356649228401681861965457 27267486921301261396474093)
            ·
              refine ⟨10225307595487973023677785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27267486921301261396474093 10225307595487973023677785)
              ·
                refine ⟨7668980696615979767758339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10225307595487973023677785 7668980696615979767758339)
                ·
                  refine ⟨11503471044923969651637509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7668980696615979767758339 11503471044923969651637509)
                  ·
                    refine ⟨2156900820923244309682033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11503471044923969651637509 2156900820923244309682033)
                    ·
                      refine ⟨1617675615692433232261525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2156900820923244309682033 1617675615692433232261525)
                      ·
                        rfl

theorem cell23_3150412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_3150412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150412 prefixEnd_3150412 := by exact prefixLift 3150412
  have htrace : WordTrace (prefixWord ++ tailWord_3150412) baseStart_3150412 baseEnd_3150412 := by
    simpa [prefixWord, tailWord_3150412, baseEnd_3150412] using wordTrace_append hprefix tailTrace_3150412
  have hstable : (prefixWord ++ tailWord_3150412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150412).length < 2 ^ (prefixWord ++ tailWord_3150412).sum := by decide
  have hdescent : baseEnd_3150412 < baseStart_3150412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150446 : List Nat := [4, 1, 2, 2, 2, 1, 2, 3, 2, 2, 2]
def baseStart_3150446 : Nat := 118140960795 + 3150446 * 2 ^ 59
def prefixEnd_3150446 : Nat := 4983230072969 + 3 ^ 40 * 3150446 * 2
def baseEnd_3150446 : Nat := 1617693074034686099236369

theorem tailTrace_3150446 : CollatzResearch.WordTrace tailWord_3150446 prefixEnd_3150446 1617693074034686099236369 := by
  unfold tailWord_3150446
  simp only [CollatzResearch.WordTrace]
  refine ⟨14363275693059958773161899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76604137029653113456863461 14363275693059958773161899)
  ·
    refine ⟨21544913539589938159742849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14363275693059958773161899 21544913539589938159742849)
    ·
      refine ⟨16158685154692453619807137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21544913539589938159742849 16158685154692453619807137)
      ·
        refine ⟨12119013866019340214855353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16158685154692453619807137 12119013866019340214855353)
        ·
          refine ⟨9089260399514505161141515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12119013866019340214855353 9089260399514505161141515)
          ·
            refine ⟨13633890599271757741712273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9089260399514505161141515 13633890599271757741712273)
            ·
              refine ⟨10225417949453818306284205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13633890599271757741712273 10225417949453818306284205)
              ·
                refine ⟨3834531731045181864856577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10225417949453818306284205 3834531731045181864856577)
                ·
                  refine ⟨2875898798283886398642433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3834531731045181864856577 2875898798283886398642433)
                  ·
                    refine ⟨2156924098712914798981825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2875898798283886398642433 2156924098712914798981825)
                    ·
                      refine ⟨1617693074034686099236369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2156924098712914798981825 1617693074034686099236369)
                      ·
                        rfl

theorem cell23_3150446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_3150446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150446 prefixEnd_3150446 := by exact prefixLift 3150446
  have htrace : WordTrace (prefixWord ++ tailWord_3150446) baseStart_3150446 baseEnd_3150446 := by
    simpa [prefixWord, tailWord_3150446, baseEnd_3150446] using wordTrace_append hprefix tailTrace_3150446
  have hstable : (prefixWord ++ tailWord_3150446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150446).length < 2 ^ (prefixWord ++ tailWord_3150446).sum := by decide
  have hdescent : baseEnd_3150446 < baseStart_3150446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150465 : List Nat := [1, 2, 4, 2, 1, 1, 3, 1, 1, 7]
def baseStart_3150465 : Nat := 118140960795 + 3150465 * 2 ^ 59
def prefixEnd_3150465 : Nat := 4983230072969 + 3 ^ 40 * 3150465 * 2
def baseEnd_3150465 : Nat := 539234276722373841632927

theorem tailTrace_3150465 : CollatzResearch.WordTrace tailWord_3150465 prefixEnd_3150465 539234276722373841632927 := by
  unfold tailWord_3150465
  simp only [CollatzResearch.WordTrace]
  refine ⟨114906898531410836430236849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76604599020940557620157899 114906898531410836430236849)
  ·
    refine ⟨86180173898558127322677637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114906898531410836430236849 86180173898558127322677637)
    ·
      refine ⟨16158782605979648873002057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86180173898558127322677637 16158782605979648873002057)
      ·
        refine ⟨12119086954484736654751543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16158782605979648873002057 12119086954484736654751543)
        ·
          refine ⟨18178630431727104982127315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12119086954484736654751543 18178630431727104982127315)
          ·
            refine ⟨27267945647590657473190973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18178630431727104982127315 27267945647590657473190973)
            ·
              refine ⟨10225479617846496552446615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27267945647590657473190973 10225479617846496552446615)
              ·
                refine ⟨15338219426769744828669923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10225479617846496552446615 15338219426769744828669923)
                ·
                  refine ⟨23007329140154617243004885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15338219426769744828669923 23007329140154617243004885)
                  ·
                    refine ⟨539234276722373841632927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23007329140154617243004885 539234276722373841632927)
                    ·
                      rfl

theorem cell23_3150465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_3150465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150465 prefixEnd_3150465 := by exact prefixLift 3150465
  have htrace : WordTrace (prefixWord ++ tailWord_3150465) baseStart_3150465 baseEnd_3150465 := by
    simpa [prefixWord, tailWord_3150465, baseEnd_3150465] using wordTrace_append hprefix tailTrace_3150465
  have hstable : (prefixWord ++ tailWord_3150465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150465).length < 2 ^ (prefixWord ++ tailWord_3150465).sum := by decide
  have hdescent : baseEnd_3150465 < baseStart_3150465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150505 : List Nat := [1, 2, 1, 1, 1, 1, 2, 6, 1, 4, 3]
def baseStart_3150505 : Nat := 118140960795 + 3150505 * 2 ^ 59
def prefixEnd_3150505 : Nat := 4983230072969 + 3 ^ 40 * 3150505 * 2
def baseEnd_3150505 : Nat := 1617723369393301368398597

theorem tailTrace_3150505 : CollatzResearch.WordTrace tailWord_3150505 prefixEnd_3150505 1617723369393301368398597 := by
  unfold tailWord_3150505
  simp only [CollatzResearch.WordTrace]
  refine ⟨114908357451265923261692969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76605571634177282174461979 114908357451265923261692969)
  ·
    refine ⟨86181268088449442446269727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114908357451265923261692969 86181268088449442446269727)
    ·
      refine ⟨129271902132674163669404591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86181268088449442446269727 129271902132674163669404591)
      ·
        refine ⟨193907853199011245504106887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129271902132674163669404591 193907853199011245504106887)
        ·
          refine ⟨290861779798516868256160331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193907853199011245504106887 290861779798516868256160331)
          ·
            refine ⟨436292669697775302384240497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290861779798516868256160331 436292669697775302384240497)
            ·
              refine ⟨327219502273331476788180373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 436292669697775302384240497 327219502273331476788180373)
              ·
                refine ⟨15338414169062412974445955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 327219502273331476788180373 15338414169062412974445955)
                ·
                  refine ⟨23007621253593619461668933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15338414169062412974445955 23007621253593619461668933)
                  ·
                    refine ⟨4313928985048803649062925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23007621253593619461668933 4313928985048803649062925)
                    ·
                      refine ⟨1617723369393301368398597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4313928985048803649062925 1617723369393301368398597)
                      ·
                        rfl

theorem cell23_3150505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 4, 3].length) (baseStart_3150505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150505 prefixEnd_3150505 := by exact prefixLift 3150505
  have htrace : WordTrace (prefixWord ++ tailWord_3150505) baseStart_3150505 baseEnd_3150505 := by
    simpa [prefixWord, tailWord_3150505, baseEnd_3150505] using wordTrace_append hprefix tailTrace_3150505
  have hstable : (prefixWord ++ tailWord_3150505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150505).length < 2 ^ (prefixWord ++ tailWord_3150505).sum := by decide
  have hdescent : baseEnd_3150505 < baseStart_3150505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150522 : List Nat := [3, 1, 1, 1, 2, 3, 2, 3, 2, 2, 3]
def baseStart_3150522 : Nat := 118140960795 + 3150522 * 2 ^ 59
def prefixEnd_3150522 : Nat := 4983230072969 + 3 ^ 40 * 3150522 * 2
def baseEnd_3150522 : Nat := 1617732098564427801886019

theorem tailTrace_3150522 : CollatzResearch.WordTrace tailWord_3150522 prefixEnd_3150522 1617732098564427801886019 := by
  unfold tailWord_3150522
  simp only [CollatzResearch.WordTrace]
  refine ⟨28727244373051083791265455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76605984994802890110041213 28727244373051083791265455)
  ·
    refine ⟨43090866559576625686898183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28727244373051083791265455 43090866559576625686898183)
    ·
      refine ⟨64636299839364938530347275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43090866559576625686898183 64636299839364938530347275)
      ·
        refine ⟨96954449759047407795520913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64636299839364938530347275 96954449759047407795520913)
        ·
          refine ⟨72715837319285555846640685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96954449759047407795520913 72715837319285555846640685)
          ·
            refine ⟨27268438994732083442490257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72715837319285555846640685 27268438994732083442490257)
            ·
              refine ⟨20451329246049062581867693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27268438994732083442490257 20451329246049062581867693)
              ·
                refine ⟨7669248467268398468200385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20451329246049062581867693 7669248467268398468200385)
                ·
                  refine ⟨5751936350451298851150289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7669248467268398468200385 5751936350451298851150289)
                  ·
                    refine ⟨4313952262838474138362717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5751936350451298851150289 4313952262838474138362717)
                    ·
                      refine ⟨1617732098564427801886019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4313952262838474138362717 1617732098564427801886019)
                      ·
                        rfl

theorem cell23_3150522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 2, 2, 3].length) (baseStart_3150522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150522 prefixEnd_3150522 := by exact prefixLift 3150522
  have htrace : WordTrace (prefixWord ++ tailWord_3150522) baseStart_3150522 baseEnd_3150522 := by
    simpa [prefixWord, tailWord_3150522, baseEnd_3150522] using wordTrace_append hprefix tailTrace_3150522
  have hstable : (prefixWord ++ tailWord_3150522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150522).length < 2 ^ (prefixWord ++ tailWord_3150522).sum := by decide
  have hdescent : baseEnd_3150522 < baseStart_3150522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150525 : List Nat := [1, 4, 1, 2, 1, 3, 1, 2, 8]
def baseStart_3150525 : Nat := 118140960795 + 3150525 * 2 ^ 59
def prefixEnd_3150525 : Nat := 4983230072969 + 3 ^ 40 * 3150525 * 2
def baseEnd_3150525 : Nat := 179748182111821254460945

theorem tailTrace_3150525 : CollatzResearch.WordTrace tailWord_3150525 prefixEnd_3150525 179748182111821254460945 := by
  unfold tailWord_3150525
  simp only [CollatzResearch.WordTrace]
  refine ⟨114909086911193466677421029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76606057940795644451614019 114909086911193466677421029)
  ·
    refine ⟨21545453795848775002016443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114909086911193466677421029 21545453795848775002016443)
    ·
      refine ⟨32318180693773162503024665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21545453795848775002016443 32318180693773162503024665)
      ·
        refine ⟨24238635520329871877268499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32318180693773162503024665 24238635520329871877268499)
        ·
          refine ⟨36357953280494807815902749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24238635520329871877268499 36357953280494807815902749)
          ·
            refine ⟨13634232480185552930963531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36357953280494807815902749 13634232480185552930963531)
            ·
              refine ⟨20451348720278329396445297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13634232480185552930963531 20451348720278329396445297)
              ·
                refine ⟨15338511540208747047333973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20451348720278329396445297 15338511540208747047333973)
                ·
                  refine ⟨179748182111821254460945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15338511540208747047333973 179748182111821254460945)
                  ·
                    rfl

theorem cell23_3150525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 8].length) (baseStart_3150525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150525 prefixEnd_3150525 := by exact prefixLift 3150525
  have htrace : WordTrace (prefixWord ++ tailWord_3150525) baseStart_3150525 baseEnd_3150525 := by
    simpa [prefixWord, tailWord_3150525, baseEnd_3150525] using wordTrace_append hprefix tailTrace_3150525
  have hstable : (prefixWord ++ tailWord_3150525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150525).length < 2 ^ (prefixWord ++ tailWord_3150525).sum := by decide
  have hdescent : baseEnd_3150525 < baseStart_3150525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150546 : List Nat := [3, 2, 2, 2, 3, 2, 1, 1, 3, 4]
def baseStart_3150546 : Nat := 118140960795 + 3150546 * 2 ^ 59
def prefixEnd_3150546 : Nat := 4983230072969 + 3 ^ 40 * 3150546 * 2
def baseEnd_3150546 : Nat := 539248140700045235995303

theorem tailTrace_3150546 : CollatzResearch.WordTrace tailWord_3150546 prefixEnd_3150546 539248140700045235995303 := by
  unfold tailWord_3150546
  simp only [CollatzResearch.WordTrace]
  refine ⟨28727463211029346815983873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76606568562744924842623661 28727463211029346815983873)
  ·
    refine ⟨21545597408272010111987905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28727463211029346815983873 21545597408272010111987905)
    ·
      refine ⟨16159198056204007583990929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21545597408272010111987905 16159198056204007583990929)
      ·
        refine ⟨12119398542153005687993197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16159198056204007583990929 12119398542153005687993197)
        ·
          refine ⟨4544774453307377132997449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12119398542153005687993197 4544774453307377132997449)
          ·
            refine ⟨3408580839980532849748087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4544774453307377132997449 3408580839980532849748087)
            ·
              refine ⟨5112871259970799274622131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3408580839980532849748087 5112871259970799274622131)
              ·
                refine ⟨7669306889956198911933197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5112871259970799274622131 7669306889956198911933197)
                ·
                  refine ⟨2875990083733574591974949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7669306889956198911933197 2875990083733574591974949)
                  ·
                    refine ⟨539248140700045235995303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2875990083733574591974949 539248140700045235995303)
                    ·
                      rfl

theorem cell23_3150546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_3150546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150546 prefixEnd_3150546 := by exact prefixLift 3150546
  have htrace : WordTrace (prefixWord ++ tailWord_3150546) baseStart_3150546 baseEnd_3150546 := by
    simpa [prefixWord, tailWord_3150546, baseEnd_3150546] using wordTrace_append hprefix tailTrace_3150546
  have hstable : (prefixWord ++ tailWord_3150546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150546).length < 2 ^ (prefixWord ++ tailWord_3150546).sum := by decide
  have hdescent : baseEnd_3150546 < baseStart_3150546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150559 : List Nat := [1, 1, 2, 3, 2, 5, 2, 1, 6]
def baseStart_3150559 : Nat := 118140960795 + 3150559 * 2 ^ 59
def prefixEnd_3150559 : Nat := 4983230072969 + 3 ^ 40 * 3150559 * 2
def baseEnd_3150559 : Nat := 179750121927627128569261

theorem tailTrace_3150559 : CollatzResearch.WordTrace tailWord_3150559 prefixEnd_3150559 179750121927627128569261 := by
  unfold tailWord_3150559
  simp only [CollatzResearch.WordTrace]
  refine ⟨114910326993070290484158731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76606884662046860322772487 114910326993070290484158731)
  ·
    refine ⟨172365490489605435726238097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114910326993070290484158731 172365490489605435726238097)
    ·
      refine ⟨129274117867204076794678573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172365490489605435726238097 129274117867204076794678573)
      ·
        refine ⟨48477794200201528798004465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129274117867204076794678573 48477794200201528798004465)
        ·
          refine ⟨36358345650151146598503349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48477794200201528798004465 36358345650151146598503349)
          ·
            refine ⟨3408594904701669993609689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36358345650151146598503349 3408594904701669993609689)
            ·
              refine ⟨2556446178526252495207267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3408594904701669993609689 2556446178526252495207267)
              ·
                refine ⟨3834669267789378742810901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2556446178526252495207267 3834669267789378742810901)
                ·
                  refine ⟨179750121927627128569261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3834669267789378742810901 179750121927627128569261)
                  ·
                    rfl

theorem cell23_3150559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 6].length) (baseStart_3150559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150559 prefixEnd_3150559 := by exact prefixLift 3150559
  have htrace : WordTrace (prefixWord ++ tailWord_3150559) baseStart_3150559 baseEnd_3150559 := by
    simpa [prefixWord, tailWord_3150559, baseEnd_3150559] using wordTrace_append hprefix tailTrace_3150559
  have hstable : (prefixWord ++ tailWord_3150559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150559).length < 2 ^ (prefixWord ++ tailWord_3150559).sum := by decide
  have hdescent : baseEnd_3150559 < baseStart_3150559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150589 : List Nat := [1, 4, 1, 1, 1, 1, 7, 1, 1, 5]
def baseStart_3150589 : Nat := 118140960795 + 3150589 * 2 ^ 59
def prefixEnd_3150589 : Nat := 4983230072969 + 3 ^ 40 * 3150589 * 2
def baseEnd_3150589 : Nat := 539255500589426346582737

theorem tailTrace_3150589 : CollatzResearch.WordTrace tailWord_3150589 prefixEnd_3150589 539255500589426346582737 := by
  unfold tailWord_3150589
  simp only [CollatzResearch.WordTrace]
  refine ⟨114911421182961605607750821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76607614121974403738500547 114911421182961605607750821)
  ·
    refine ⟨21545891471805301051453279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114911421182961605607750821 21545891471805301051453279)
    ·
      refine ⟨32318837207707951577179919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21545891471805301051453279 32318837207707951577179919)
      ·
        refine ⟨48478255811561927365769879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32318837207707951577179919 48478255811561927365769879)
        ·
          refine ⟨72717383717342891048654819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48478255811561927365769879 72717383717342891048654819)
          ·
            refine ⟨109076075576014336572982229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72717383717342891048654819 109076075576014336572982229)
            ·
              refine ⟨2556470521312836013429271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 109076075576014336572982229 2556470521312836013429271)
              ·
                refine ⟨3834705781969254020143907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2556470521312836013429271 3834705781969254020143907)
                ·
                  refine ⟨5752058672953881030215861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3834705781969254020143907 5752058672953881030215861)
                  ·
                    refine ⟨539255500589426346582737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5752058672953881030215861 539255500589426346582737)
                    ·
                      rfl

theorem cell23_3150589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_3150589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150589 prefixEnd_3150589 := by exact prefixLift 3150589
  have htrace : WordTrace (prefixWord ++ tailWord_3150589) baseStart_3150589 baseEnd_3150589 := by
    simpa [prefixWord, tailWord_3150589, baseEnd_3150589] using wordTrace_append hprefix tailTrace_3150589
  have hstable : (prefixWord ++ tailWord_3150589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150589).length < 2 ^ (prefixWord ++ tailWord_3150589).sum := by decide
  have hdescent : baseEnd_3150589 < baseStart_3150589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150626 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2]
def baseStart_3150626 : Nat := 118140960795 + 3150626 * 2 ^ 59
def prefixEnd_3150626 : Nat := 4983230072969 + 3 ^ 40 * 3150626 * 2
def baseEnd_3150626 : Nat := 1617785500552495394985541

theorem tailTrace_3150626 : CollatzResearch.WordTrace tailWord_3150626 prefixEnd_3150626 1617785500552495394985541 := by
  unfold tailWord_3150626
  simp only [CollatzResearch.WordTrace]
  refine ⟨28728192670956890231711933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76608513789218373951231821 28728192670956890231711933)
  ·
    refine ⟨10773072251608833836891975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28728192670956890231711933 10773072251608833836891975)
    ·
      refine ⟨16159608377413250755337963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10773072251608833836891975 16159608377413250755337963)
      ·
        refine ⟨24239412566119876133006945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16159608377413250755337963 24239412566119876133006945)
        ·
          refine ⟨18179559424589907099755209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24239412566119876133006945 18179559424589907099755209)
          ·
            refine ⟨13634669568442430324816407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18179559424589907099755209 13634669568442430324816407)
            ·
              refine ⟨20452004352663645487224611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13634669568442430324816407 20452004352663645487224611)
              ·
                refine ⟨30678006528995468230836917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20452004352663645487224611 30678006528995468230836917)
                ·
                  refine ⟨2876063112093325146640961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30678006528995468230836917 2876063112093325146640961)
                  ·
                    refine ⟨2157047334069993859980721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2876063112093325146640961 2157047334069993859980721)
                    ·
                      refine ⟨1617785500552495394985541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2157047334069993859980721 1617785500552495394985541)
                      ·
                        rfl

theorem cell23_3150626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_3150626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150626 prefixEnd_3150626 := by exact prefixLift 3150626
  have htrace : WordTrace (prefixWord ++ tailWord_3150626) baseStart_3150626 baseEnd_3150626 := by
    simpa [prefixWord, tailWord_3150626, baseEnd_3150626] using wordTrace_append hprefix tailTrace_3150626
  have hstable : (prefixWord ++ tailWord_3150626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150626).length < 2 ^ (prefixWord ++ tailWord_3150626).sum := by decide
  have hdescent : baseEnd_3150626 < baseStart_3150626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150629 : List Nat := [1, 3, 1, 2, 3, 1, 2, 4, 1, 2, 3]
def baseStart_3150629 : Nat := 118140960795 + 3150629 * 2 ^ 59
def prefixEnd_3150629 : Nat := 4983230072969 + 3 ^ 40 * 3150629 * 2
def baseEnd_3150629 : Nat := 1617787040994458883248027

theorem tailTrace_3150629 : CollatzResearch.WordTrace tailWord_3150629 prefixEnd_3150629 1617787040994458883248027 := by
  unfold tailWord_3150629
  simp only [CollatzResearch.WordTrace]
  refine ⟨114912880102816692439206941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76608586735211128292804627 114912880102816692439206941)
  ·
    refine ⟨43092330038556259664702603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114912880102816692439206941 43092330038556259664702603)
    ·
      refine ⟨64638495057834389497053905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43092330038556259664702603 64638495057834389497053905)
      ·
        refine ⟨48478871293375792122790429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64638495057834389497053905 48478871293375792122790429)
        ·
          refine ⟨18179576735015922046046411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48478871293375792122790429 18179576735015922046046411)
          ·
            refine ⟨27269365102523883069069617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18179576735015922046046411 27269365102523883069069617)
            ·
              refine ⟨20452023826892912301802213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27269365102523883069069617 20452023826892912301802213)
              ·
                refine ⟨3834754467542421056587915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20452023826892912301802213 3834754467542421056587915)
                ·
                  refine ⟨5752131701313631584881873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3834754467542421056587915 5752131701313631584881873)
                  ·
                    refine ⟨4314098775985223688661405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5752131701313631584881873 4314098775985223688661405)
                    ·
                      refine ⟨1617787040994458883248027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4314098775985223688661405 1617787040994458883248027)
                      ·
                        rfl

theorem cell23_3150629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_3150629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150629 prefixEnd_3150629 := by exact prefixLift 3150629
  have htrace : WordTrace (prefixWord ++ tailWord_3150629) baseStart_3150629 baseEnd_3150629 := by
    simpa [prefixWord, tailWord_3150629, baseEnd_3150629] using wordTrace_append hprefix tailTrace_3150629
  have hstable : (prefixWord ++ tailWord_3150629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150629).length < 2 ^ (prefixWord ++ tailWord_3150629).sum := by decide
  have hdescent : baseEnd_3150629 < baseStart_3150629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150637 : List Nat := [1, 5, 3, 2, 1, 1, 2, 3, 1, 1, 3]
def baseStart_3150637 : Nat := 118140960795 + 3150637 * 2 ^ 59
def prefixEnd_3150637 : Nat := 4983230072969 + 3 ^ 40 * 3150637 * 2
def baseEnd_3150637 : Nat := 1617791148839694851947991

theorem tailTrace_3150637 : CollatzResearch.WordTrace tailWord_3150637 prefixEnd_3150637 1617791148839694851947991 := by
  unfold tailWord_3150637
  simp only [CollatzResearch.WordTrace]
  refine ⟨114913171886787709805498165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76608781257858473203665443 114913171886787709805498165)
  ·
    refine ⟨10773109864386347794265453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114913171886787709805498165 10773109864386347794265453)
    ·
      refine ⟨4039916199144880422849545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10773109864386347794265453 4039916199144880422849545)
      ·
        refine ⟨3029937149358660317137159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4039916199144880422849545 3029937149358660317137159)
        ·
          refine ⟨4544905724037990475705739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3029937149358660317137159 4544905724037990475705739)
          ·
            refine ⟨6817358586056985713558609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4544905724037990475705739 6817358586056985713558609)
            ·
              refine ⟨5113018939542739285168957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6817358586056985713558609 5113018939542739285168957)
              ·
                refine ⟨1917382102328527231938359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5113018939542739285168957 1917382102328527231938359)
                ·
                  refine ⟨2876073153492790847907539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1917382102328527231938359 2876073153492790847907539)
                  ·
                    refine ⟨4314109730239186271861309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2876073153492790847907539 4314109730239186271861309)
                    ·
                      refine ⟨1617791148839694851947991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4314109730239186271861309 1617791148839694851947991)
                      ·
                        rfl

theorem cell23_3150637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_3150637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150637 prefixEnd_3150637 := by exact prefixLift 3150637
  have htrace : WordTrace (prefixWord ++ tailWord_3150637) baseStart_3150637 baseEnd_3150637 := by
    simpa [prefixWord, tailWord_3150637, baseEnd_3150637] using wordTrace_append hprefix tailTrace_3150637
  have hstable : (prefixWord ++ tailWord_3150637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150637).length < 2 ^ (prefixWord ++ tailWord_3150637).sum := by decide
  have hdescent : baseEnd_3150637 < baseStart_3150637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150643 : List Nat := [1, 1, 1, 2, 6, 1, 1, 5, 1, 2, 2]
def baseStart_3150643 : Nat := 118140960795 + 3150643 * 2 ^ 59
def prefixEnd_3150643 : Nat := 4983230072969 + 3 ^ 40 * 3150643 * 2
def baseEnd_3150643 : Nat := 1617794229723621828472963

theorem tailTrace_3150643 : CollatzResearch.WordTrace tailWord_3150643 prefixEnd_3150643 1617794229723621828472963 := by
  unfold tailWord_3150643
  simp only [CollatzResearch.WordTrace]
  refine ⟨114913390724765972830216583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76608927149843981886811055 114913390724765972830216583)
  ·
    refine ⟨172370086087148959245324875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114913390724765972830216583 172370086087148959245324875)
    ·
      refine ⟨258555129130723438867987313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172370086087148959245324875 258555129130723438867987313)
      ·
        refine ⟨193916346848042579150990485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258555129130723438867987313 193916346848042579150990485)
        ·
          refine ⟨9089828758501995897702679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 193916346848042579150990485 9089828758501995897702679)
          ·
            refine ⟨13634743137752993846554019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9089828758501995897702679 13634743137752993846554019)
            ·
              refine ⟨20452114706629490769831029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13634743137752993846554019 20452114706629490769831029)
              ·
                refine ⟨1917385753746514759671659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20452114706629490769831029 1917385753746514759671659)
                ·
                  refine ⟨2876078630619772139507489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1917385753746514759671659 2876078630619772139507489)
                  ·
                    refine ⟨2157058972964829104630617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2876078630619772139507489 2157058972964829104630617)
                    ·
                      refine ⟨1617794229723621828472963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2157058972964829104630617 1617794229723621828472963)
                      ·
                        rfl

theorem cell23_3150643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 5, 1, 2, 2].length) (baseStart_3150643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150643 prefixEnd_3150643 := by exact prefixLift 3150643
  have htrace : WordTrace (prefixWord ++ tailWord_3150643) baseStart_3150643 baseEnd_3150643 := by
    simpa [prefixWord, tailWord_3150643, baseEnd_3150643] using wordTrace_append hprefix tailTrace_3150643
  have hstable : (prefixWord ++ tailWord_3150643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150643).length < 2 ^ (prefixWord ++ tailWord_3150643).sum := by decide
  have hdescent : baseEnd_3150643 < baseStart_3150643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150653 : List Nat := [1, 4, 1, 4, 2, 2, 1, 2, 2, 4]
def baseStart_3150653 : Nat := 118140960795 + 3150653 * 2 ^ 59
def prefixEnd_3150653 : Nat := 4983230072969 + 3 ^ 40 * 3150653 * 2
def baseEnd_3150653 : Nat := 539266454843388929782639

theorem tailTrace_3150653 : CollatzResearch.WordTrace tailWord_3150653 prefixEnd_3150653 539266454843388929782639 := by
  unfold tailWord_3150653
  simp only [CollatzResearch.WordTrace]
  refine ⟨114913755454729744538080613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76609170303153163025387075 114913755454729744538080613)
  ·
    refine ⟨21546329147761827100890115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114913755454729744538080613 21546329147761827100890115)
    ·
      refine ⟨32319493721642740651335173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21546329147761827100890115 32319493721642740651335173)
      ·
        refine ⟨6059905072808013872125345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32319493721642740651335173 6059905072808013872125345)
        ·
          refine ⟨4544928804606010404094009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6059905072808013872125345 4544928804606010404094009)
          ·
            refine ⟨3408696603454507803070507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4544928804606010404094009 3408696603454507803070507)
            ·
              refine ⟨5113044905181761704605761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3408696603454507803070507 5113044905181761704605761)
              ·
                refine ⟨3834783678886321278454321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5113044905181761704605761 3834783678886321278454321)
                ·
                  refine ⟨2876087759164740958840741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3834783678886321278454321 2876087759164740958840741)
                  ·
                    refine ⟨539266454843388929782639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2876087759164740958840741 539266454843388929782639)
                    ·
                      rfl

theorem cell23_3150653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_3150653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150653 prefixEnd_3150653 := by exact prefixLift 3150653
  have htrace : WordTrace (prefixWord ++ tailWord_3150653) baseStart_3150653 baseEnd_3150653 := by
    simpa [prefixWord, tailWord_3150653, baseEnd_3150653] using wordTrace_append hprefix tailTrace_3150653
  have hstable : (prefixWord ++ tailWord_3150653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150653).length < 2 ^ (prefixWord ++ tailWord_3150653).sum := by decide
  have hdescent : baseEnd_3150653 < baseStart_3150653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150659 : List Nat := [1, 1, 1, 3, 1, 4, 3, 1, 4, 1, 3]
def baseStart_3150659 : Nat := 118140960795 + 3150659 * 2 ^ 59
def prefixEnd_3150659 : Nat := 4983230072969 + 3 ^ 40 * 3150659 * 2
def baseEnd_3150659 : Nat := 1617802445414093765872889

theorem tailTrace_3150659 : CollatzResearch.WordTrace tailWord_3150659 prefixEnd_3150659 1617802445414093765872889 := by
  unfold tailWord_3150659
  simp only [CollatzResearch.WordTrace]
  refine ⟨114913974292708007562799031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76609316195138671708532687 114913974292708007562799031)
  ·
    refine ⟨172370961439062011344198547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114913974292708007562799031 172370961439062011344198547)
    ·
      refine ⟨258556442158593017016297821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172370961439062011344198547 258556442158593017016297821)
      ·
        refine ⟨96958665809472381381111683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258556442158593017016297821 96958665809472381381111683)
        ·
          refine ⟨145437998714208572071667525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96958665809472381381111683 145437998714208572071667525)
          ·
            refine ⟨27269624758914107263437661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145437998714208572071667525 27269624758914107263437661)
            ·
              refine ⟨10226109284592790223789123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27269624758914107263437661 10226109284592790223789123)
              ·
                refine ⟨15339163926889185335683685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10226109284592790223789123 15339163926889185335683685)
                ·
                  refine ⟨2876093236291722250440691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15339163926889185335683685 2876093236291722250440691)
                  ·
                    refine ⟨4314139854437583375661037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2876093236291722250440691 4314139854437583375661037)
                    ·
                      refine ⟨1617802445414093765872889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4314139854437583375661037 1617802445414093765872889)
                      ·
                        rfl

theorem cell23_3150659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 4, 1, 3].length) (baseStart_3150659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150659 prefixEnd_3150659 := by exact prefixLift 3150659
  have htrace : WordTrace (prefixWord ++ tailWord_3150659) baseStart_3150659 baseEnd_3150659 := by
    simpa [prefixWord, tailWord_3150659, baseEnd_3150659] using wordTrace_append hprefix tailTrace_3150659
  have hstable : (prefixWord ++ tailWord_3150659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150659).length < 2 ^ (prefixWord ++ tailWord_3150659).sum := by decide
  have hdescent : baseEnd_3150659 < baseStart_3150659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150699 : List Nat := [1, 1, 1, 1, 2, 2, 4, 4, 1, 4, 2]
def baseStart_3150699 : Nat := 118140960795 + 3150699 * 2 ^ 59
def prefixEnd_3150699 : Nat := 4983230072969 + 3 ^ 40 * 3150699 * 2
def baseEnd_3150699 : Nat := 1617822984640273609372705

theorem tailTrace_3150699 : CollatzResearch.WordTrace tailWord_3150699 prefixEnd_3150699 1617822984640273609372705 := by
  unfold tailWord_3150699
  simp only [CollatzResearch.WordTrace]
  refine ⟨114915433212563094394255151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76610288808375396262836767 114915433212563094394255151)
  ·
    refine ⟨172373149818844641591382727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114915433212563094394255151 172373149818844641591382727)
    ·
      refine ⟨258559724728266962387074091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172373149818844641591382727 258559724728266962387074091)
      ·
        refine ⟨387839587092400443580611137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258559724728266962387074091 387839587092400443580611137)
        ·
          refine ⟨290879690319300332685458353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387839587092400443580611137 290879690319300332685458353)
          ·
            refine ⟨218159767739475249514093765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290879690319300332685458353 218159767739475249514093765)
            ·
              refine ⟨40904956451151609283892581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 218159767739475249514093765 40904956451151609283892581)
              ·
                refine ⟨7669679334590926740729859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40904956451151609283892581 7669679334590926740729859)
                ·
                  refine ⟨11504519001886390111094789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7669679334590926740729859 11504519001886390111094789)
                  ·
                    refine ⟨2157097312853698145830273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11504519001886390111094789 2157097312853698145830273)
                    ·
                      refine ⟨1617822984640273609372705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2157097312853698145830273 1617822984640273609372705)
                      ·
                        rfl

theorem cell23_3150699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 4, 2].length) (baseStart_3150699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150699 prefixEnd_3150699 := by exact prefixLift 3150699
  have htrace : WordTrace (prefixWord ++ tailWord_3150699) baseStart_3150699 baseEnd_3150699 := by
    simpa [prefixWord, tailWord_3150699, baseEnd_3150699] using wordTrace_append hprefix tailTrace_3150699
  have hstable : (prefixWord ++ tailWord_3150699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150699).length < 2 ^ (prefixWord ++ tailWord_3150699).sum := by decide
  have hdescent : baseEnd_3150699 < baseStart_3150699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150712 : List Nat := [2, 1, 2, 1, 1, 1, 1, 6, 2, 2, 4]
def baseStart_3150712 : Nat := 118140960795 + 3150712 * 2 ^ 59
def prefixEnd_3150712 : Nat := 4983230072969 + 3 ^ 40 * 3150712 * 2
def baseEnd_3150712 : Nat := 1617829659888782058510145

theorem tailTrace_3150712 : CollatzResearch.WordTrace tailWord_3150712 prefixEnd_3150712 1617829659888782058510145 := by
  unfold tailWord_3150712
  simp only [CollatzResearch.WordTrace]
  refine ⟨57457953680757998807239195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76610604907677331742985593 57457953680757998807239195)
  ·
    refine ⟨86186930521136998210858793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57457953680757998807239195 86186930521136998210858793)
    ·
      refine ⟨64640197890852748658144095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86186930521136998210858793 64640197890852748658144095)
      ·
        refine ⟨96960296836279122987216143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64640197890852748658144095 96960296836279122987216143)
        ·
          refine ⟨145440445254418684480824215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96960296836279122987216143 145440445254418684480824215)
          ·
            refine ⟨218160667881628026721236323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145440445254418684480824215 218160667881628026721236323)
            ·
              refine ⟨327241001822442040081854485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218160667881628026721236323 327241001822442040081854485)
              ·
                refine ⟨15339421960426970628836929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 327241001822442040081854485 15339421960426970628836929)
                ·
                  refine ⟨11504566470320227971627697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15339421960426970628836929 11504566470320227971627697)
                  ·
                    refine ⟨8628424852740170978720773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11504566470320227971627697 8628424852740170978720773)
                    ·
                      refine ⟨1617829659888782058510145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8628424852740170978720773 1617829659888782058510145)
                      ·
                        rfl

theorem cell23_3150712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_3150712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150712 prefixEnd_3150712 := by exact prefixLift 3150712
  have htrace : WordTrace (prefixWord ++ tailWord_3150712) baseStart_3150712 baseEnd_3150712 := by
    simpa [prefixWord, tailWord_3150712, baseEnd_3150712] using wordTrace_append hprefix tailTrace_3150712
  have hstable : (prefixWord ++ tailWord_3150712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150712).length < 2 ^ (prefixWord ++ tailWord_3150712).sum := by decide
  have hdescent : baseEnd_3150712 < baseStart_3150712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150752 : List Nat := [2, 1, 1, 4, 1, 1, 2, 3, 1, 7]
def baseStart_3150752 : Nat := 118140960795 + 3150752 * 2 ^ 59
def prefixEnd_3150752 : Nat := 4983230072969 + 3 ^ 40 * 3150752 * 2
def baseEnd_3150752 : Nat := 539283399704987300669987

theorem tailTrace_3150752 : CollatzResearch.WordTrace tailWord_3150752 prefixEnd_3150752 539283399704987300669987 := by
  unfold tailWord_3150752
  simp only [CollatzResearch.WordTrace]
  refine ⟨57458683140685542222967255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76611577520914056297289673 57458683140685542222967255)
  ·
    refine ⟨86188024711028313334450883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57458683140685542222967255 86188024711028313334450883)
    ·
      refine ⟨129282037066542470001676325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86188024711028313334450883 129282037066542470001676325)
      ·
        refine ⟨24240381949976713125314311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129282037066542470001676325 24240381949976713125314311)
        ·
          refine ⟨36360572924965069687971467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24240381949976713125314311 36360572924965069687971467)
          ·
            refine ⟨54540859387447604531957201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36360572924965069687971467 54540859387447604531957201)
            ·
              refine ⟨40905644540585703398967901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54540859387447604531957201 40905644540585703398967901)
              ·
                refine ⟨15339616702719638774612963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40905644540585703398967901 15339616702719638774612963)
                ·
                  refine ⟨23009425054079458161919445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15339616702719638774612963 23009425054079458161919445)
                  ·
                    refine ⟨539283399704987300669987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23009425054079458161919445 539283399704987300669987)
                    ·
                      rfl

theorem cell23_3150752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 1, 7].length) (baseStart_3150752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150752 prefixEnd_3150752 := by exact prefixLift 3150752
  have htrace : WordTrace (prefixWord ++ tailWord_3150752) baseStart_3150752 baseEnd_3150752 := by
    simpa [prefixWord, tailWord_3150752, baseEnd_3150752] using wordTrace_append hprefix tailTrace_3150752
  have hstable : (prefixWord ++ tailWord_3150752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150752).length < 2 ^ (prefixWord ++ tailWord_3150752).sum := by decide
  have hdescent : baseEnd_3150752 < baseStart_3150752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150799 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 5, 4]
def baseStart_3150799 : Nat := 118140960795 + 3150799 * 2 ^ 59
def prefixEnd_3150799 : Nat := 4983230072969 + 3 ^ 40 * 3150799 * 2
def baseEnd_3150799 : Nat := 539291444235241072707415

theorem tailTrace_3150799 : CollatzResearch.WordTrace tailWord_3150799 prefixEnd_3150799 539291444235241072707415 := by
  unfold tailWord_3150799
  simp only [CollatzResearch.WordTrace]
  refine ⟨114919080512200811472895451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76612720341467207648596967 114919080512200811472895451)
  ·
    refine ⟨172378620768301217209343177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114919080512200811472895451 172378620768301217209343177)
    ·
      refine ⟨129283965576225912907007383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172378620768301217209343177 129283965576225912907007383)
      ·
        refine ⟨193925948364338869360511075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129283965576225912907007383 193925948364338869360511075)
        ·
          refine ⟨290888922546508304040766613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193925948364338869360511075 290888922546508304040766613)
          ·
            refine ⟨13635418244367576751910935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 290888922546508304040766613 13635418244367576751910935)
            ·
              refine ⟨20453127366551365127866403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13635418244367576751910935 20453127366551365127866403)
              ·
                refine ⟨30679691049827047691799605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20453127366551365127866403 30679691049827047691799605)
                ·
                  refine ⟨2876221035921285721106213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30679691049827047691799605 2876221035921285721106213)
                  ·
                    refine ⟨539291444235241072707415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2876221035921285721106213 539291444235241072707415)
                    ·
                      rfl

theorem cell23_3150799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 5, 4].length) (baseStart_3150799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150799 prefixEnd_3150799 := by exact prefixLift 3150799
  have htrace : WordTrace (prefixWord ++ tailWord_3150799) baseStart_3150799 baseEnd_3150799 := by
    simpa [prefixWord, tailWord_3150799, baseEnd_3150799] using wordTrace_append hprefix tailTrace_3150799
  have hstable : (prefixWord ++ tailWord_3150799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150799).length < 2 ^ (prefixWord ++ tailWord_3150799).sum := by decide
  have hdescent : baseEnd_3150799 < baseStart_3150799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150833 : List Nat := [1, 2, 2, 2, 4, 1, 2, 4, 1, 4]
def baseStart_3150833 : Nat := 118140960795 + 3150833 * 2 ^ 59
def prefixEnd_3150833 : Nat := 4983230072969 + 3 ^ 40 * 3150833 * 2
def baseEnd_3150833 : Nat := 539297263682658695032363

theorem tailTrace_3150833 : CollatzResearch.WordTrace tailWord_3150833 prefixEnd_3150833 539297263682658695032363 := by
  unfold tailWord_3150833
  simp only [CollatzResearch.WordTrace]
  refine ⟨114920320594077635279633153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76613547062718423519755435 114920320594077635279633153)
  ·
    refine ⟨86190240445558226459724865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114920320594077635279633153 86190240445558226459724865)
    ·
      refine ⟨64642680334168669844793649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86190240445558226459724865 64642680334168669844793649)
      ·
        refine ⟨48482010250626502383595237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64642680334168669844793649 48482010250626502383595237)
        ·
          refine ⟨9090376921992469196924107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48482010250626502383595237 9090376921992469196924107)
          ·
            refine ⟨13635565382988703795386161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9090376921992469196924107 13635565382988703795386161)
            ·
              refine ⟨10226674037241527846539621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13635565382988703795386161 10226674037241527846539621)
              ·
                refine ⟨1917501381982786471226179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10226674037241527846539621 1917501381982786471226179)
                ·
                  refine ⟨2876252072974179706839269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1917501381982786471226179 2876252072974179706839269)
                  ·
                    refine ⟨539297263682658695032363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2876252072974179706839269 539297263682658695032363)
                    ·
                      rfl

theorem cell23_3150833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 4, 1, 4].length) (baseStart_3150833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150833 prefixEnd_3150833 := by exact prefixLift 3150833
  have htrace : WordTrace (prefixWord ++ tailWord_3150833) baseStart_3150833 baseEnd_3150833 := by
    simpa [prefixWord, tailWord_3150833, baseEnd_3150833] using wordTrace_append hprefix tailTrace_3150833
  have hstable : (prefixWord ++ tailWord_3150833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150833).length < 2 ^ (prefixWord ++ tailWord_3150833).sum := by decide
  have hdescent : baseEnd_3150833 < baseStart_3150833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150883 : List Nat := [1, 1, 1, 4, 3, 3, 1, 2, 2, 3, 2]
def baseStart_3150883 : Nat := 118140960795 + 3150883 * 2 ^ 59
def prefixEnd_3150883 : Nat := 4983230072969 + 3 ^ 40 * 3150883 * 2
def baseEnd_3150883 : Nat := 1617917465080700889471859

theorem tailTrace_3150883 : CollatzResearch.WordTrace tailWord_3150883 prefixEnd_3150883 1617917465080700889471859 := by
  unfold tailWord_3150883
  simp only [CollatzResearch.WordTrace]
  refine ⟨114922144243896493818953303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76614762829264329212635535 114922144243896493818953303)
  ·
    refine ⟨172383216365844740728429955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114922144243896493818953303 172383216365844740728429955)
    ·
      refine ⟨258574824548767111092644933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172383216365844740728429955 258574824548767111092644933)
      ·
        refine ⟨48482779602893833329870925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 258574824548767111092644933 48482779602893833329870925)
        ·
          refine ⟨18181042351085187498701597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48482779602893833329870925 18181042351085187498701597)
          ·
            refine ⟨6817890881656945312013099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18181042351085187498701597 6817890881656945312013099)
            ·
              refine ⟨10226836322485417968019649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6817890881656945312013099 10226836322485417968019649)
              ·
                refine ⟨7670127241864063476014737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10226836322485417968019649 7670127241864063476014737)
                ·
                  refine ⟨5752595431398047607011053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7670127241864063476014737 5752595431398047607011053)
                  ·
                    refine ⟨2157223286774267852629145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5752595431398047607011053 2157223286774267852629145)
                    ·
                      refine ⟨1617917465080700889471859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2157223286774267852629145 1617917465080700889471859)
                      ·
                        rfl

theorem cell23_3150883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 3, 2].length) (baseStart_3150883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150883 prefixEnd_3150883 := by exact prefixLift 3150883
  have htrace : WordTrace (prefixWord ++ tailWord_3150883) baseStart_3150883 baseEnd_3150883 := by
    simpa [prefixWord, tailWord_3150883, baseEnd_3150883] using wordTrace_append hprefix tailTrace_3150883
  have hstable : (prefixWord ++ tailWord_3150883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150883).length < 2 ^ (prefixWord ++ tailWord_3150883).sum := by decide
  have hdescent : baseEnd_3150883 < baseStart_3150883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150899 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 2, 6, 3]
def baseStart_3150899 : Nat := 118140960795 + 3150899 * 2 ^ 59
def prefixEnd_3150899 : Nat := 4983230072969 + 3 ^ 40 * 3150899 * 2
def baseEnd_3150899 : Nat := 1617925680771172826871785

theorem tailTrace_3150899 : CollatzResearch.WordTrace tailWord_3150899 prefixEnd_3150899 1617925680771172826871785 := by
  unfold tailWord_3150899
  simp only [CollatzResearch.WordTrace]
  refine ⟨114922727811838528551535751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76615151874559019034357167 114922727811838528551535751)
  ·
    refine ⟨172384091717757792827303627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114922727811838528551535751 172384091717757792827303627)
    ·
      refine ⟨258576137576636689240955441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172384091717757792827303627 258576137576636689240955441)
      ·
        refine ⟨193932103182477516930716581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258576137576636689240955441 193932103182477516930716581)
        ·
          refine ⟨36362269346714534424509359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193932103182477516930716581 36362269346714534424509359)
          ·
            refine ⟨54543404020071801636764039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36362269346714534424509359 54543404020071801636764039)
            ·
              refine ⟨81815106030107702455146059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54543404020071801636764039 81815106030107702455146059)
              ·
                refine ⟨122722659045161553682719089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81815106030107702455146059 122722659045161553682719089)
                ·
                  refine ⟨92041994283871165262039317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122722659045161553682719089 92041994283871165262039317)
                  ·
                    refine ⟨4314468482056460871658093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92041994283871165262039317 4314468482056460871658093)
                    ·
                      refine ⟨1617925680771172826871785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4314468482056460871658093 1617925680771172826871785)
                      ·
                        rfl

theorem cell23_3150899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 6, 3].length) (baseStart_3150899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150899 prefixEnd_3150899 := by exact prefixLift 3150899
  have htrace : WordTrace (prefixWord ++ tailWord_3150899) baseStart_3150899 baseEnd_3150899 := by
    simpa [prefixWord, tailWord_3150899, baseEnd_3150899] using wordTrace_append hprefix tailTrace_3150899
  have hstable : (prefixWord ++ tailWord_3150899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150899).length < 2 ^ (prefixWord ++ tailWord_3150899).sum := by decide
  have hdescent : baseEnd_3150899 < baseStart_3150899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150910 : List Nat := [4, 2, 1, 3, 1, 3, 1, 2, 1, 5]
def baseStart_3150910 : Nat := 118140960795 + 3150910 * 2 ^ 59
def prefixEnd_3150910 : Nat := 4983230072969 + 3 ^ 40 * 3150910 * 2
def baseEnd_3150910 : Nat := 539310443019457427944745

theorem tailTrace_3150910 : CollatzResearch.WordTrace tailWord_3150910 prefixEnd_3150910 539310443019457427944745 := by
  unfold tailWord_3150910
  simp only [CollatzResearch.WordTrace]
  refine ⟨14365391126849834678773273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76615419343199118286790789 14365391126849834678773273)
  ·
    refine ⟨10774043345137376009079955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14365391126849834678773273 10774043345137376009079955)
    ·
      refine ⟨16161065017706064013619933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10774043345137376009079955 16161065017706064013619933)
      ·
        refine ⟨6060399381639774005107475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16161065017706064013619933 6060399381639774005107475)
        ·
          refine ⟨9090599072459661007661213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6060399381639774005107475 9090599072459661007661213)
          ·
            refine ⟨3408974652172372877872955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9090599072459661007661213 3408974652172372877872955)
            ·
              refine ⟨5113461978258559316809433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3408974652172372877872955 5113461978258559316809433)
              ·
                refine ⟨3835096483693919487607075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5113461978258559316809433 3835096483693919487607075)
                ·
                  refine ⟨5752644725540879231410613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3835096483693919487607075 5752644725540879231410613)
                  ·
                    refine ⟨539310443019457427944745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5752644725540879231410613 539310443019457427944745)
                    ·
                      rfl

theorem cell23_3150910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_3150910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150910 prefixEnd_3150910 := by exact prefixLift 3150910
  have htrace : WordTrace (prefixWord ++ tailWord_3150910) baseStart_3150910 baseEnd_3150910 := by
    simpa [prefixWord, tailWord_3150910, baseEnd_3150910] using wordTrace_append hprefix tailTrace_3150910
  have hstable : (prefixWord ++ tailWord_3150910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150910).length < 2 ^ (prefixWord ++ tailWord_3150910).sum := by decide
  have hdescent : baseEnd_3150910 < baseStart_3150910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150913 : List Nat := [1, 2, 5, 1, 3, 1, 1, 1, 3, 1, 4]
def baseStart_3150913 : Nat := 118140960795 + 3150913 * 2 ^ 59
def prefixEnd_3150913 : Nat := 4983230072969 + 3 ^ 40 * 3150913 * 2
def baseEnd_3150913 : Nat := 1617932869500335772096721

theorem tailTrace_3150913 : CollatzResearch.WordTrace tailWord_3150913 prefixEnd_3150913 1617932869500335772096721 := by
  unfold tailWord_3150913
  simp only [CollatzResearch.WordTrace]
  refine ⟨114923238433787808942545393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76615492289191872628363595 114923238433787808942545393)
  ·
    refine ⟨86192428825340856706909045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114923238433787808942545393 86192428825340856706909045)
    ·
      refine ⟨8080540202375705316272723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86192428825340856706909045 8080540202375705316272723)
      ·
        refine ⟨12120810303563557974409085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8080540202375705316272723 12120810303563557974409085)
        ·
          refine ⟨4545303863836334240403407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12120810303563557974409085 4545303863836334240403407)
          ·
            refine ⟨6817955795754501360605111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4545303863836334240403407 6817955795754501360605111)
            ·
              refine ⟨10226933693631752040907667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6817955795754501360605111 10226933693631752040907667)
              ·
                refine ⟨15340400540447628061361501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10226933693631752040907667 15340400540447628061361501)
                ·
                  refine ⟨5752650202667860523010563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15340400540447628061361501 5752650202667860523010563)
                  ·
                    refine ⟨8628975304001790784515845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5752650202667860523010563 8628975304001790784515845)
                    ·
                      refine ⟨1617932869500335772096721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8628975304001790784515845 1617932869500335772096721)
                      ·
                        rfl

theorem cell23_3150913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_3150913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150913 prefixEnd_3150913 := by exact prefixLift 3150913
  have htrace : WordTrace (prefixWord ++ tailWord_3150913) baseStart_3150913 baseEnd_3150913 := by
    simpa [prefixWord, tailWord_3150913, baseEnd_3150913] using wordTrace_append hprefix tailTrace_3150913
  have hstable : (prefixWord ++ tailWord_3150913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150913).length < 2 ^ (prefixWord ++ tailWord_3150913).sum := by decide
  have hdescent : baseEnd_3150913 < baseStart_3150913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150919 : List Nat := [1, 1, 4, 1, 3, 2, 2, 9]
def baseStart_3150919 : Nat := 118140960795 + 3150919 * 2 ^ 59
def prefixEnd_3150919 : Nat := 4983230072969 + 3 ^ 40 * 3150919 * 2
def baseEnd_3150919 : Nat := 59923553717935657356359

theorem tailTrace_3150919 : CollatzResearch.WordTrace tailWord_3150919 prefixEnd_3150919 59923553717935657356359 := by
  unfold tailWord_3150919
  simp only [CollatzResearch.WordTrace]
  refine ⟨114923457271766071967263811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76615638181177381311509207 114923457271766071967263811)
  ·
    refine ⟨172385185907649107950895717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114923457271766071967263811 172385185907649107950895717)
    ·
      refine ⟨32322222357684207740792947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172385185907649107950895717 32322222357684207740792947)
      ·
        refine ⟨48483333536526311611189421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32322222357684207740792947 48483333536526311611189421)
        ·
          refine ⟨18181250076197366854196033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48483333536526311611189421 18181250076197366854196033)
          ·
            refine ⟨13635937557148025140647025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18181250076197366854196033 13635937557148025140647025)
            ·
              refine ⟨10226953167861018855485269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13635937557148025140647025 10226953167861018855485269)
              ·
                refine ⟨59923553717935657356359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10226953167861018855485269 59923553717935657356359)
                ·
                  rfl

theorem cell23_3150919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 9].length) (baseStart_3150919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150919 prefixEnd_3150919 := by exact prefixLift 3150919
  have htrace : WordTrace (prefixWord ++ tailWord_3150919) baseStart_3150919 baseEnd_3150919 := by
    simpa [prefixWord, tailWord_3150919, baseEnd_3150919] using wordTrace_append hprefix tailTrace_3150919
  have hstable : (prefixWord ++ tailWord_3150919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150919).length < 2 ^ (prefixWord ++ tailWord_3150919).sum := by decide
  have hdescent : baseEnd_3150919 < baseStart_3150919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150926 : List Nat := [4, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4]
def baseStart_3150926 : Nat := 118140960795 + 3150926 * 2 ^ 59
def prefixEnd_3150926 : Nat := 4983230072969 + 3 ^ 40 * 3150926 * 2
def baseEnd_3150926 : Nat := 1617939544748844221234161

theorem tailTrace_3150926 : CollatzResearch.WordTrace tailWord_3150926 prefixEnd_3150926 1617939544748844221234161 := by
  unfold tailWord_3150926
  simp only [CollatzResearch.WordTrace]
  refine ⟨14365464072842589020346079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76615808388493808108512421 14365464072842589020346079)
  ·
    refine ⟨21548196109263883530519119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14365464072842589020346079 21548196109263883530519119)
    ·
      refine ⟨32322294163895825295778679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21548196109263883530519119 32322294163895825295778679)
      ·
        refine ⟨48483441245843737943668019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32322294163895825295778679 48483441245843737943668019)
        ·
          refine ⟨72725161868765606915502029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48483441245843737943668019 72725161868765606915502029)
          ·
            refine ⟨27271935700787102593313261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72725161868765606915502029 27271935700787102593313261)
            ·
              refine ⟨10226975887795163472492473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27271935700787102593313261 10226975887795163472492473)
              ·
                refine ⟨7670231915846372604369355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10226975887795163472492473 7670231915846372604369355)
                ·
                  refine ⟨11505347873769558906554033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7670231915846372604369355 11505347873769558906554033)
                  ·
                    refine ⟨8629010905327169179915525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11505347873769558906554033 8629010905327169179915525)
                    ·
                      refine ⟨1617939544748844221234161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8629010905327169179915525 1617939544748844221234161)
                      ·
                        rfl

theorem cell23_3150926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_3150926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150926 prefixEnd_3150926 := by exact prefixLift 3150926
  have htrace : WordTrace (prefixWord ++ tailWord_3150926) baseStart_3150926 baseEnd_3150926 := by
    simpa [prefixWord, tailWord_3150926, baseEnd_3150926] using wordTrace_append hprefix tailTrace_3150926
  have hstable : (prefixWord ++ tailWord_3150926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150926).length < 2 ^ (prefixWord ++ tailWord_3150926).sum := by decide
  have hdescent : baseEnd_3150926 < baseStart_3150926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150930 : List Nat := [3, 2, 2, 1, 3, 2, 3, 1, 1, 1, 4]
def baseStart_3150930 : Nat := 118140960795 + 3150930 * 2 ^ 59
def prefixEnd_3150930 : Nat := 4983230072969 + 3 ^ 40 * 3150930 * 2
def baseEnd_3150930 : Nat := 1617941598671462205584143

theorem tailTrace_3150930 : CollatzResearch.WordTrace tailWord_3150930 prefixEnd_3150930 1617941598671462205584143 := by
  unfold tailWord_3150930
  simp only [CollatzResearch.WordTrace]
  refine ⟨28730964618681555211478561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76615905649817480563942829 28730964618681555211478561)
  ·
    refine ⟨21548223464011166408608921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28730964618681555211478561 21548223464011166408608921)
    ·
      refine ⟨16161167598008374806456691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21548223464011166408608921 16161167598008374806456691)
      ·
        refine ⟨24241751397012562209685037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16161167598008374806456691 24241751397012562209685037)
        ·
          refine ⟨9090656773879710828631889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24241751397012562209685037 9090656773879710828631889)
          ·
            refine ⟨6817992580409783121473917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9090656773879710828631889 6817992580409783121473917)
            ·
              refine ⟨2556747217653668670552719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6817992580409783121473917 2556747217653668670552719)
              ·
                refine ⟨3835120826480503005829079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2556747217653668670552719 3835120826480503005829079)
                ·
                  refine ⟨5752681239720754508743619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3835120826480503005829079 5752681239720754508743619)
                  ·
                    refine ⟨8629021859581131763115429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5752681239720754508743619 8629021859581131763115429)
                    ·
                      refine ⟨1617941598671462205584143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8629021859581131763115429 1617941598671462205584143)
                      ·
                        rfl

theorem cell23_3150930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_3150930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150930 prefixEnd_3150930 := by exact prefixLift 3150930
  have htrace : WordTrace (prefixWord ++ tailWord_3150930) baseStart_3150930 baseEnd_3150930 := by
    simpa [prefixWord, tailWord_3150930, baseEnd_3150930] using wordTrace_append hprefix tailTrace_3150930
  have hstable : (prefixWord ++ tailWord_3150930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150930).length < 2 ^ (prefixWord ++ tailWord_3150930).sum := by decide
  have hdescent : baseEnd_3150930 < baseStart_3150930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150941 : List Nat := [1, 4, 4, 1, 2, 2, 2, 2, 1, 1, 3]
def baseStart_3150941 : Nat := 118140960795 + 3150941 * 2 ^ 59
def prefixEnd_3150941 : Nat := 4983230072969 + 3 ^ 40 * 3150941 * 2
def baseEnd_3150941 : Nat := 1617947246958661662546593

theorem tailTrace_3150941 : CollatzResearch.WordTrace tailWord_3150941 prefixEnd_3150941 1617947246958661662546593 := by
  unfold tailWord_3150941
  simp only [CollatzResearch.WordTrace]
  refine ⟨114924259677686369724564677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76616173118457579816376451 114924259677686369724564677)
  ·
    refine ⟨21548298689566194323355877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114924259677686369724564677 21548298689566194323355877)
    ·
      refine ⟨4040306004293661435629227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21548298689566194323355877 4040306004293661435629227)
      ·
        refine ⟨6060459006440492153443841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4040306004293661435629227 6060459006440492153443841)
        ·
          refine ⟨4545344254830369115082881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6060459006440492153443841 4545344254830369115082881)
          ·
            refine ⟨3409008191122776836312161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4545344254830369115082881 3409008191122776836312161)
            ·
              refine ⟨2556756143342082627234121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3409008191122776836312161 2556756143342082627234121)
              ·
                refine ⟨1917567107506561970425591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2556756143342082627234121 1917567107506561970425591)
                ·
                  refine ⟨2876350661259842955638387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1917567107506561970425591 2876350661259842955638387)
                  ·
                    refine ⟨4314525991889764433457581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2876350661259842955638387 4314525991889764433457581)
                    ·
                      refine ⟨1617947246958661662546593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4314525991889764433457581 1617947246958661662546593)
                      ·
                        rfl

theorem cell23_3150941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_3150941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150941 prefixEnd_3150941 := by exact prefixLift 3150941
  have htrace : WordTrace (prefixWord ++ tailWord_3150941) baseStart_3150941 baseEnd_3150941 := by
    simpa [prefixWord, tailWord_3150941, baseEnd_3150941] using wordTrace_append hprefix tailTrace_3150941
  have hstable : (prefixWord ++ tailWord_3150941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150941).length < 2 ^ (prefixWord ++ tailWord_3150941).sum := by decide
  have hdescent : baseEnd_3150941 < baseStart_3150941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150949 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 1, 9]
def baseStart_3150949 : Nat := 118140960795 + 3150949 * 2 ^ 59
def prefixEnd_3150949 : Nat := 4983230072969 + 3 ^ 40 * 3150949 * 2
def baseEnd_3150949 : Nat := 539317118267965877082185

theorem tailTrace_3150949 : CollatzResearch.WordTrace tailWord_3150949 prefixEnd_3150949 539317118267965877082185 := by
  unfold tailWord_3150949
  simp only [CollatzResearch.WordTrace]
  refine ⟨114924551461657387090855901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76616367641104924727237267 114924551461657387090855901)
  ·
    refine ⟨43096706798121520159070963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114924551461657387090855901 43096706798121520159070963)
    ·
      refine ⟨64645060197182280238606445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43096706798121520159070963 64645060197182280238606445)
      ·
        refine ⟨24241897573943355089477417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64645060197182280238606445 24241897573943355089477417)
        ·
          refine ⟨18181423180457516317108063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24241897573943355089477417 18181423180457516317108063)
          ·
            refine ⟨27272134770686274475662095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18181423180457516317108063 27272134770686274475662095)
            ·
              refine ⟨40908202156029411713493143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27272134770686274475662095 40908202156029411713493143)
              ·
                refine ⟨61362303234044117570239715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40908202156029411713493143 61362303234044117570239715)
                ·
                  refine ⟨92043454851066176355359573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61362303234044117570239715 92043454851066176355359573)
                  ·
                    refine ⟨539317118267965877082185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 92043454851066176355359573 539317118267965877082185)
                    ·
                      rfl

theorem cell23_3150949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 9].length) (baseStart_3150949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150949 prefixEnd_3150949 := by exact prefixLift 3150949
  have htrace : WordTrace (prefixWord ++ tailWord_3150949) baseStart_3150949 baseEnd_3150949 := by
    simpa [prefixWord, tailWord_3150949, baseEnd_3150949] using wordTrace_append hprefix tailTrace_3150949
  have hstable : (prefixWord ++ tailWord_3150949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150949).length < 2 ^ (prefixWord ++ tailWord_3150949).sum := by decide
  have hdescent : baseEnd_3150949 < baseStart_3150949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150966 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 2, 7]
def baseStart_3150966 : Nat := 118140960795 + 3150966 * 2 ^ 59
def prefixEnd_3150966 : Nat := 4983230072969 + 3 ^ 40 * 3150966 * 2
def baseEnd_3150966 : Nat := 539320027991674688244659

theorem tailTrace_3150966 : CollatzResearch.WordTrace tailWord_3150966 prefixEnd_3150966 539320027991674688244659 := by
  unfold tailWord_3150966
  simp only [CollatzResearch.WordTrace]
  refine ⟨7182823218912237437139047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76616781001730532662816501 7182823218912237437139047)
  ·
    refine ⟨10774234828368356155708571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7182823218912237437139047 10774234828368356155708571)
    ·
      refine ⟨16161352242552534233562857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10774234828368356155708571 16161352242552534233562857)
      ·
        refine ⟨12121014181914400675172143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16161352242552534233562857 12121014181914400675172143)
        ·
          refine ⟨18181521272871601012758215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12121014181914400675172143 18181521272871601012758215)
          ·
            refine ⟨27272281909307401519137323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18181521272871601012758215 27272281909307401519137323)
            ·
              refine ⟨40908422863961102278705985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27272281909307401519137323 40908422863961102278705985)
              ·
                refine ⟨30681317147970826709029489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40908422863961102278705985 30681317147970826709029489)
                ·
                  refine ⟨23010987860978120031772117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30681317147970826709029489 23010987860978120031772117)
                  ·
                    refine ⟨539320027991674688244659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23010987860978120031772117 539320027991674688244659)
                    ·
                      rfl

theorem cell23_3150966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_3150966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150966 prefixEnd_3150966 := by exact prefixLift 3150966
  have htrace : WordTrace (prefixWord ++ tailWord_3150966) baseStart_3150966 baseEnd_3150966 := by
    simpa [prefixWord, tailWord_3150966, baseEnd_3150966] using wordTrace_append hprefix tailTrace_3150966
  have hstable : (prefixWord ++ tailWord_3150966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150966).length < 2 ^ (prefixWord ++ tailWord_3150966).sum := by decide
  have hdescent : baseEnd_3150966 < baseStart_3150966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150973 : List Nat := [1, 4, 1, 1, 3, 1, 1, 3, 3, 3, 2]
def baseStart_3150973 : Nat := 118140960795 + 3150973 * 2 ^ 59
def prefixEnd_3150973 : Nat := 4983230072969 + 3 ^ 40 * 3150973 * 2
def baseEnd_3150973 : Nat := 1617963678339605537346445

theorem tailTrace_3150973 : CollatzResearch.WordTrace tailWord_3150973 prefixEnd_3150973 1617963678339605537346445 := by
  unfold tailWord_3150973
  simp only [CollatzResearch.WordTrace]
  refine ⟨114925426813570439189729573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76616951209046959459819715 114925426813570439189729573)
  ·
    refine ⟨21548517527544457348074295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114925426813570439189729573 21548517527544457348074295)
    ·
      refine ⟨32322776291316686022111443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21548517527544457348074295 32322776291316686022111443)
      ·
        refine ⟨48484164436975029033167165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32322776291316686022111443 48484164436975029033167165)
        ·
          refine ⟨18181561663865635887437687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48484164436975029033167165 18181561663865635887437687)
          ·
            refine ⟨27272342495798453831156531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18181561663865635887437687 27272342495798453831156531)
            ·
              refine ⟨40908513743697680746734797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27272342495798453831156531 40908513743697680746734797)
              ·
                refine ⟨15340692653886630280025549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40908513743697680746734797 15340692653886630280025549)
                ·
                  refine ⟨5752759745207486355009581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15340692653886630280025549 5752759745207486355009581)
                  ·
                    refine ⟨2157284904452807383128593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5752759745207486355009581 2157284904452807383128593)
                    ·
                      refine ⟨1617963678339605537346445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2157284904452807383128593 1617963678339605537346445)
                      ·
                        rfl

theorem cell23_3150973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 3, 2].length) (baseStart_3150973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150973 prefixEnd_3150973 := by exact prefixLift 3150973
  have htrace : WordTrace (prefixWord ++ tailWord_3150973) baseStart_3150973 baseEnd_3150973 := by
    simpa [prefixWord, tailWord_3150973, baseEnd_3150973] using wordTrace_append hprefix tailTrace_3150973
  have hstable : (prefixWord ++ tailWord_3150973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150973).length < 2 ^ (prefixWord ++ tailWord_3150973).sum := by decide
  have hdescent : baseEnd_3150973 < baseStart_3150973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150979 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 1, 8]
def baseStart_3150979 : Nat := 118140960795 + 3150979 * 2 ^ 59
def prefixEnd_3150979 : Nat := 4983230072969 + 3 ^ 40 * 3150979 * 2
def baseEnd_3150979 : Nat := 539322253074510837957139

theorem tailTrace_3150979 : CollatzResearch.WordTrace tailWord_3150979 prefixEnd_3150979 539322253074510837957139 := by
  unfold tailWord_3150979
  simp only [CollatzResearch.WordTrace]
  refine ⟨114925645651548702214447991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76617097101032468142965327 114925645651548702214447991)
  ·
    refine ⟨172388468477323053321671987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114925645651548702214447991 172388468477323053321671987)
    ·
      refine ⟨258582702715984579982507981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172388468477323053321671987 258582702715984579982507981)
      ·
        refine ⟨96968513518494217493440493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258582702715984579982507981 96968513518494217493440493)
        ·
          refine ⟨36363192569435331560040185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96968513518494217493440493 36363192569435331560040185)
          ·
            refine ⟨27272394427076498670030139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36363192569435331560040185 27272394427076498670030139)
            ·
              refine ⟨40908591640614748005045209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27272394427076498670030139 40908591640614748005045209)
              ·
                refine ⟨30681443730461061003783907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40908591640614748005045209 30681443730461061003783907)
                ·
                  refine ⟨46022165595691591505675861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30681443730461061003783907 46022165595691591505675861)
                  ·
                    refine ⟨539322253074510837957139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46022165595691591505675861 539322253074510837957139)
                    ·
                      rfl

theorem cell23_3150979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 8].length) (baseStart_3150979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150979 prefixEnd_3150979 := by exact prefixLift 3150979
  have htrace : WordTrace (prefixWord ++ tailWord_3150979) baseStart_3150979 baseEnd_3150979 := by
    simpa [prefixWord, tailWord_3150979, baseEnd_3150979] using wordTrace_append hprefix tailTrace_3150979
  have hstable : (prefixWord ++ tailWord_3150979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150979).length < 2 ^ (prefixWord ++ tailWord_3150979).sum := by decide
  have hdescent : baseEnd_3150979 < baseStart_3150979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150984 : List Nat := [2, 1, 3, 4, 3, 1, 2, 1, 1, 2, 3]
def baseStart_3150984 : Nat := 118140960795 + 3150984 * 2 ^ 59
def prefixEnd_3150984 : Nat := 4983230072969 + 3 ^ 40 * 3150984 * 2
def baseEnd_3150984 : Nat := 1617969326626804994308895

theorem tailTrace_3150984 : CollatzResearch.WordTrace tailWord_3150984 prefixEnd_3150984 1617969326626804994308895 := by
  unfold tailWord_3150984
  simp only [CollatzResearch.WordTrace]
  refine ⟨57462914008265294034190003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76617218677687058712253337 57462914008265294034190003)
  ·
    refine ⟨86194371012397941051285005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57462914008265294034190003 86194371012397941051285005)
    ·
      refine ⟨32322889129649227894231877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86194371012397941051285005 32322889129649227894231877)
      ·
        refine ⟨6060541711809230230168477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32322889129649227894231877 6060541711809230230168477)
        ·
          refine ⟨2272703141928461336313179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6060541711809230230168477 2272703141928461336313179)
          ·
            refine ⟨3409054712892692004469769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2272703141928461336313179 3409054712892692004469769)
            ·
              refine ⟨2556791034669519003352327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3409054712892692004469769 2556791034669519003352327)
              ·
                refine ⟨3835186552004278505028491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2556791034669519003352327 3835186552004278505028491)
                ·
                  refine ⟨5752779828006417757542737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3835186552004278505028491 5752779828006417757542737)
                  ·
                    refine ⟨4314584871004813318157053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5752779828006417757542737 4314584871004813318157053)
                    ·
                      refine ⟨1617969326626804994308895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4314584871004813318157053 1617969326626804994308895)
                      ·
                        rfl

theorem cell23_3150984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_3150984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3150984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3150984 prefixEnd_3150984 := by exact prefixLift 3150984
  have htrace : WordTrace (prefixWord ++ tailWord_3150984) baseStart_3150984 baseEnd_3150984 := by
    simpa [prefixWord, tailWord_3150984, baseEnd_3150984] using wordTrace_append hprefix tailTrace_3150984
  have hstable : (prefixWord ++ tailWord_3150984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150984).length < 2 ^ (prefixWord ++ tailWord_3150984).sum := by decide
  have hdescent : baseEnd_3150984 < baseStart_3150984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151026 : List Nat := [3, 2, 1, 1, 1, 4, 2, 2, 7]
def baseStart_3151026 : Nat := 118140960795 + 3151026 * 2 ^ 59
def prefixEnd_3151026 : Nat := 4983230072969 + 3 ^ 40 * 3151026 * 2
def baseEnd_3151026 : Nat := 179776765868254869998189

theorem tailTrace_3151026 : CollatzResearch.WordTrace tailWord_3151026 prefixEnd_3151026 179776765868254869998189 := by
  unfold tailWord_3151026
  simp only [CollatzResearch.WordTrace]
  refine ⟨28731839970594607310352233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76618239921585619494272621 28731839970594607310352233)
  ·
    refine ⟨21548879977945955482764175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28731839970594607310352233 21548879977945955482764175)
    ·
      refine ⟨32323319966918933224146263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21548879977945955482764175 32323319966918933224146263)
      ·
        refine ⟨48484979950378399836219395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32323319966918933224146263 48484979950378399836219395)
        ·
          refine ⟨72727469925567599754329093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48484979950378399836219395 72727469925567599754329093)
          ·
            refine ⟨13636400611043924953936705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72727469925567599754329093 13636400611043924953936705)
            ·
              refine ⟨10227300458282943715452529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13636400611043924953936705 10227300458282943715452529)
              ·
                refine ⟨7670475343712207786589397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10227300458282943715452529 7670475343712207786589397)
                ·
                  refine ⟨179776765868254869998189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7670475343712207786589397 179776765868254869998189)
                  ·
                    rfl

theorem cell23_3151026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 7].length) (baseStart_3151026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151026 prefixEnd_3151026 := by exact prefixLift 3151026
  have htrace : WordTrace (prefixWord ++ tailWord_3151026) baseStart_3151026 baseEnd_3151026 := by
    simpa [prefixWord, tailWord_3151026, baseEnd_3151026] using wordTrace_append hprefix tailTrace_3151026
  have hstable : (prefixWord ++ tailWord_3151026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151026).length < 2 ^ (prefixWord ++ tailWord_3151026).sum := by decide
  have hdescent : baseEnd_3151026 < baseStart_3151026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151076 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 3, 3, 4]
def baseStart_3151076 : Nat := 118140960795 + 3151076 * 2 ^ 59
def prefixEnd_3151076 : Nat := 4983230072969 + 3 ^ 40 * 3151076 * 2
def baseEnd_3151076 : Nat := 1618016566847018634358471

theorem tailTrace_3151076 : CollatzResearch.WordTrace tailWord_3151076 prefixEnd_3151076 1618016566847018634358471 := by
  unfold tailWord_3151076
  simp only [CollatzResearch.WordTrace]
  refine ⟨57464591766098643890364541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76619455688131525187152721 57464591766098643890364541)
  ·
    refine ⟨21549221912286991458886703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57464591766098643890364541 21549221912286991458886703)
    ·
      refine ⟨32323832868430487188330055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21549221912286991458886703 32323832868430487188330055)
      ·
        refine ⟨48485749302645730782495083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32323832868430487188330055 48485749302645730782495083)
        ·
          refine ⟨72728623953968596173742625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48485749302645730782495083 72728623953968596173742625)
          ·
            refine ⟨54546467965476447130306969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72728623953968596173742625 54546467965476447130306969)
            ·
              refine ⟨40909850974107335347730227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54546467965476447130306969 40909850974107335347730227)
              ·
                refine ⟨61364776461161003021595341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40909850974107335347730227 61364776461161003021595341)
                ·
                  refine ⟨23011791172935376133098253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61364776461161003021595341 23011791172935376133098253)
                  ·
                    refine ⟨8629421689850766049911845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23011791172935376133098253 8629421689850766049911845)
                    ·
                      refine ⟨1618016566847018634358471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8629421689850766049911845 1618016566847018634358471)
                      ·
                        rfl

theorem cell23_3151076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_3151076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151076 prefixEnd_3151076 := by exact prefixLift 3151076
  have htrace : WordTrace (prefixWord ++ tailWord_3151076) baseStart_3151076 baseEnd_3151076 := by
    simpa [prefixWord, tailWord_3151076, baseEnd_3151076] using wordTrace_append hprefix tailTrace_3151076
  have hstable : (prefixWord ++ tailWord_3151076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151076).length < 2 ^ (prefixWord ++ tailWord_3151076).sum := by decide
  have hdescent : baseEnd_3151076 < baseStart_3151076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151086 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 2, 8]
def baseStart_3151086 : Nat := 118140960795 + 3151086 * 2 ^ 59
def prefixEnd_3151086 : Nat := 4983230072969 + 3 ^ 40 * 3151086 * 2
def baseEnd_3151086 : Nat := 539340567217854531744475

theorem tailTrace_3151086 : CollatzResearch.WordTrace tailWord_3151086 prefixEnd_3151086 539340567217854531744475 := by
  unfold tailWord_3151086
  simp only [CollatzResearch.WordTrace]
  refine ⟨14366193532770132436074139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76619698841440706325728741 14366193532770132436074139)
  ·
    refine ⟨21549290299155198654111209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14366193532770132436074139 21549290299155198654111209)
    ·
      refine ⟨16161967724366398990583407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21549290299155198654111209 16161967724366398990583407)
      ·
        refine ⟨24242951586549598485875111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16161967724366398990583407 24242951586549598485875111)
        ·
          refine ⟨36364427379824397728812667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24242951586549598485875111 36364427379824397728812667)
          ·
            refine ⟨54546641069736596593219001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36364427379824397728812667 54546641069736596593219001)
            ·
              refine ⟨40909980802302447444914251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54546641069736596593219001 40909980802302447444914251)
              ·
                refine ⟨61364971203453671167371377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40909980802302447444914251 61364971203453671167371377)
                ·
                  refine ⟨46023728402590253375528533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61364971203453671167371377 46023728402590253375528533)
                  ·
                    refine ⟨539340567217854531744475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46023728402590253375528533 539340567217854531744475)
                    ·
                      rfl

theorem cell23_3151086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_3151086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151086 prefixEnd_3151086 := by exact prefixLift 3151086
  have htrace : WordTrace (prefixWord ++ tailWord_3151086) baseStart_3151086 baseEnd_3151086 := by
    simpa [prefixWord, tailWord_3151086, baseEnd_3151086] using wordTrace_append hprefix tailTrace_3151086
  have hstable : (prefixWord ++ tailWord_3151086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151086).length < 2 ^ (prefixWord ++ tailWord_3151086).sum := by decide
  have hdescent : baseEnd_3151086 < baseStart_3151086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151090 : List Nat := [3, 2, 1, 3, 3, 1, 2, 1, 2, 5]
def baseStart_3151090 : Nat := 118140960795 + 3151090 * 2 ^ 59
def prefixEnd_3151090 : Nat := 4983230072969 + 3 ^ 40 * 3151090 * 2
def baseEnd_3151090 : Nat := 539341251858727193194469

theorem tailTrace_3151090 : CollatzResearch.WordTrace tailWord_3151090 prefixEnd_3151090 539341251858727193194469 := by
  unfold tailWord_3151090
  simp only [CollatzResearch.WordTrace]
  refine ⟨28732423538536642042934681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76619796102764378781159149 28732423538536642042934681)
  ·
    refine ⟨21549317653902481532201011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28732423538536642042934681 21549317653902481532201011)
    ·
      refine ⟨32323976480853722298301517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21549317653902481532201011 32323976480853722298301517)
      ·
        refine ⟨12121491180320145861863069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32323976480853722298301517 12121491180320145861863069)
        ·
          refine ⟨4545559192620054698198651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12121491180320145861863069 4545559192620054698198651)
          ·
            refine ⟨6818338788930082047297977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4545559192620054698198651 6818338788930082047297977)
            ·
              refine ⟨5113754091697561535473483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6818338788930082047297977 5113754091697561535473483)
              ·
                refine ⟨7670631137546342303210225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5113754091697561535473483 7670631137546342303210225)
                ·
                  refine ⟨5752973353159756727407669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7670631137546342303210225 5752973353159756727407669)
                  ·
                    refine ⟨539341251858727193194469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5752973353159756727407669 539341251858727193194469)
                    ·
                      rfl

theorem cell23_3151090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_3151090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151090 prefixEnd_3151090 := by exact prefixLift 3151090
  have htrace : WordTrace (prefixWord ++ tailWord_3151090) baseStart_3151090 baseEnd_3151090 := by
    simpa [prefixWord, tailWord_3151090, baseEnd_3151090] using wordTrace_append hprefix tailTrace_3151090
  have hstable : (prefixWord ++ tailWord_3151090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151090).length < 2 ^ (prefixWord ++ tailWord_3151090).sum := by decide
  have hdescent : baseEnd_3151090 < baseStart_3151090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151113 : List Nat := [1, 2, 1, 1, 3, 3, 1, 4, 2, 2, 3]
def baseStart_3151113 : Nat := 118140960795 + 3151113 * 2 ^ 59
def prefixEnd_3151113 : Nat := 4983230072969 + 3 ^ 40 * 3151113 * 2
def baseEnd_3151113 : Nat := 1618035565631234989595801

theorem tailTrace_3151113 : CollatzResearch.WordTrace tailWord_3151113 prefixEnd_3151113 1618035565631234989595801 := by
  unfold tailWord_3151113
  simp only [CollatzResearch.WordTrace]
  refine ⟨114930533033063243099825993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76620355355375495399883995 114930533033063243099825993)
  ·
    refine ⟨86197899774797432324869495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114930533033063243099825993 86197899774797432324869495)
    ·
      refine ⟨129296849662196148487304243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86197899774797432324869495 129296849662196148487304243)
      ·
        refine ⟨193945274493294222730956365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129296849662196148487304243 193945274493294222730956365)
        ·
          refine ⟨72729477934985333524108637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193945274493294222730956365 72729477934985333524108637)
          ·
            refine ⟨27273554225619500071540739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72729477934985333524108637 27273554225619500071540739)
            ·
              refine ⟨40910331338429250107311109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27273554225619500071540739 40910331338429250107311109)
              ·
                refine ⟨7670687125955484395120833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40910331338429250107311109 7670687125955484395120833)
                ·
                  refine ⟨5753015344466613296340625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7670687125955484395120833 5753015344466613296340625)
                  ·
                    refine ⟨4314761508349959972255469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5753015344466613296340625 4314761508349959972255469)
                    ·
                      refine ⟨1618035565631234989595801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4314761508349959972255469 1618035565631234989595801)
                      ·
                        rfl

theorem cell23_3151113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 2, 3].length) (baseStart_3151113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151113 prefixEnd_3151113 := by exact prefixLift 3151113
  have htrace : WordTrace (prefixWord ++ tailWord_3151113) baseStart_3151113 baseEnd_3151113 := by
    simpa [prefixWord, tailWord_3151113, baseEnd_3151113] using wordTrace_append hprefix tailTrace_3151113
  have hstable : (prefixWord ++ tailWord_3151113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151113).length < 2 ^ (prefixWord ++ tailWord_3151113).sum := by decide
  have hdescent : baseEnd_3151113 < baseStart_3151113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151177 : List Nat := [1, 2, 1, 1, 2, 3, 4, 4, 1, 1, 3]
def baseStart_3151177 : Nat := 118140960795 + 3151177 * 2 ^ 59
def prefixEnd_3151177 : Nat := 4983230072969 + 3 ^ 40 * 3151177 * 2
def baseEnd_3151177 : Nat := 1618068428393122739195507

theorem tailTrace_3151177 : CollatzResearch.WordTrace tailWord_3151177 prefixEnd_3151177 1618068428393122739195507 := by
  unfold tailWord_3151177
  simp only [CollatzResearch.WordTrace]
  refine ⟨114932867304831382030155785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76621911536554254686770523 114932867304831382030155785)
  ·
    refine ⟨86199650478623536522616839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114932867304831382030155785 86199650478623536522616839)
    ·
      refine ⟨129299475717935304783925259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86199650478623536522616839 129299475717935304783925259)
      ·
        refine ⟨193949213576902957175887889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129299475717935304783925259 193949213576902957175887889)
        ·
          refine ⟨145461910182677217881915917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193949213576902957175887889 145461910182677217881915917)
          ·
            refine ⟨54548216318503956705718469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145461910182677217881915917 54548216318503956705718469)
            ·
              refine ⟨10227790559719491882322213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54548216318503956705718469 10227790559719491882322213)
              ·
                refine ⟨1917710729947404727935415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10227790559719491882322213 1917710729947404727935415)
                ·
                  refine ⟨2876566094921107091903123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1917710729947404727935415 2876566094921107091903123)
                  ·
                    refine ⟨4314849142381660637854685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2876566094921107091903123 4314849142381660637854685)
                    ·
                      refine ⟨1618068428393122739195507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4314849142381660637854685 1618068428393122739195507)
                      ·
                        rfl

theorem cell23_3151177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 4, 1, 1, 3].length) (baseStart_3151177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151177 prefixEnd_3151177 := by exact prefixLift 3151177
  have htrace : WordTrace (prefixWord ++ tailWord_3151177) baseStart_3151177 baseEnd_3151177 := by
    simpa [prefixWord, tailWord_3151177, baseEnd_3151177] using wordTrace_append hprefix tailTrace_3151177
  have hstable : (prefixWord ++ tailWord_3151177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151177).length < 2 ^ (prefixWord ++ tailWord_3151177).sum := by decide
  have hdescent : baseEnd_3151177 < baseStart_3151177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151193 : List Nat := [1, 2, 1, 2, 2, 2, 5, 1, 1, 6]
def baseStart_3151193 : Nat := 118140960795 + 3151193 * 2 ^ 59
def prefixEnd_3151193 : Nat := 4983230072969 + 3 ^ 40 * 3151193 * 2
def baseEnd_3151193 : Nat := 539358881361198225531811

theorem tailTrace_3151193 : CollatzResearch.WordTrace tailWord_3151193 prefixEnd_3151193 539358881361198225531811 := by
  unfold tailWord_3151193
  simp only [CollatzResearch.WordTrace]
  refine ⟨114933450872773416762738233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76622300581848944508492155 114933450872773416762738233)
  ·
    refine ⟨86200088154580062572053675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114933450872773416762738233 86200088154580062572053675)
    ·
      refine ⟨129300132231870093858080513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86200088154580062572053675 129300132231870093858080513)
      ·
        refine ⟨96975099173902570393560385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129300132231870093858080513 96975099173902570393560385)
        ·
          refine ⟨72731324380426927795170289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96975099173902570393560385 72731324380426927795170289)
          ·
            refine ⟨54548493285320195846377717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72731324380426927795170289 54548493285320195846377717)
            ·
              refine ⟨5113921245498768360597911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54548493285320195846377717 5113921245498768360597911)
              ·
                refine ⟨7670881868248152540896867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5113921245498768360597911 7670881868248152540896867)
                ·
                  refine ⟨11506322802372228811345301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7670881868248152540896867 11506322802372228811345301)
                  ·
                    refine ⟨539358881361198225531811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11506322802372228811345301 539358881361198225531811)
                    ·
                      rfl

theorem cell23_3151193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 6].length) (baseStart_3151193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151193 prefixEnd_3151193 := by exact prefixLift 3151193
  have htrace : WordTrace (prefixWord ++ tailWord_3151193) baseStart_3151193 baseEnd_3151193 := by
    simpa [prefixWord, tailWord_3151193, baseEnd_3151193] using wordTrace_append hprefix tailTrace_3151193
  have hstable : (prefixWord ++ tailWord_3151193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151193).length < 2 ^ (prefixWord ++ tailWord_3151193).sum := by decide
  have hdescent : baseEnd_3151193 < baseStart_3151193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151200 : List Nat := [2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 4]
def baseStart_3151200 : Nat := 118140960795 + 3151200 * 2 ^ 59
def prefixEnd_3151200 : Nat := 4983230072969 + 3 ^ 40 * 3151200 * 2
def baseEnd_3151200 : Nat := 1618080238448176149207901

theorem tailTrace_3151200 : CollatzResearch.WordTrace tailWord_3151200 prefixEnd_3151200 1618080238448176149207901 := by
  unfold tailWord_3151200
  simp only [CollatzResearch.WordTrace]
  refine ⟨57466853091874028479121527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76622470789165371305495369 57466853091874028479121527)
  ·
    refine ⟨86200279637811042718682291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57466853091874028479121527 86200279637811042718682291)
    ·
      refine ⟨129300419456716564078023437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86200279637811042718682291 129300419456716564078023437)
      ·
        refine ⟨48487657296268711529258789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129300419456716564078023437 48487657296268711529258789)
        ·
          refine ⟨9091435743050383411736023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48487657296268711529258789 9091435743050383411736023)
          ·
            refine ⟨13637153614575575117604035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9091435743050383411736023 13637153614575575117604035)
            ·
              refine ⟨20455730421863362676406053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13637153614575575117604035 20455730421863362676406053)
              ·
                refine ⟨3835449454099380501826135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20455730421863362676406053 3835449454099380501826135)
                ·
                  refine ⟨5753174181149070752739203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3835449454099380501826135 5753174181149070752739203)
                  ·
                    refine ⟨8629761271723606129108805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5753174181149070752739203 8629761271723606129108805)
                    ·
                      refine ⟨1618080238448176149207901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8629761271723606129108805 1618080238448176149207901)
                      ·
                        rfl

theorem cell23_3151200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_3151200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3151200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3151200 prefixEnd_3151200 := by exact prefixLift 3151200
  have htrace : WordTrace (prefixWord ++ tailWord_3151200) baseStart_3151200 baseEnd_3151200 := by
    simpa [prefixWord, tailWord_3151200, baseEnd_3151200] using wordTrace_append hprefix tailTrace_3151200
  have hstable : (prefixWord ++ tailWord_3151200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151200).length < 2 ^ (prefixWord ++ tailWord_3151200).sum := by decide
  have hdescent : baseEnd_3151200 < baseStart_3151200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
