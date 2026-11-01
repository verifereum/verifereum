Theory vfmTest2857[no_sig_docs]
Ancestors vfmTestDefs2857
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2857_0.nsv", "result2857_1.nsv"];
val thyn = "vfmTestDefs2857";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
