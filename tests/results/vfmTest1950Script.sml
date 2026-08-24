Theory vfmTest1950[no_sig_docs]
Ancestors vfmTestDefs1950
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1950_0.nsv", "result1950_1.nsv", "result1950_2.nsv", "result1950_3.nsv"];
val thyn = "vfmTestDefs1950";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
