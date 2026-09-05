Theory vfmTest1034[no_sig_docs]
Ancestors vfmTestDefs1034
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1034_0.nsv", "result1034_1.nsv"];
val thyn = "vfmTestDefs1034";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
