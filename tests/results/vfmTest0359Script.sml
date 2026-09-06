Theory vfmTest0359[no_sig_docs]
Ancestors vfmTestDefs0359
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0359_0.nsv"];
val thyn = "vfmTestDefs0359";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
