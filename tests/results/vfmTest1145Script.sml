Theory vfmTest1145[no_sig_docs]
Ancestors vfmTestDefs1145
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1145_0.nsv", "result1145_1.nsv"];
val thyn = "vfmTestDefs1145";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
