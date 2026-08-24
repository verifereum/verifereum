Theory vfmTest2205[no_sig_docs]
Ancestors vfmTestDefs2205
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2205_0.nsv", "result2205_1.nsv", "result2205_2.nsv"];
val thyn = "vfmTestDefs2205";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
