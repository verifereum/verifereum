Theory vfmTest1945[no_sig_docs]
Ancestors vfmTestDefs1945
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1945_0.nsv", "result1945_1.nsv"];
val thyn = "vfmTestDefs1945";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
