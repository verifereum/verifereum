Theory vfmTest1889[no_sig_docs]
Ancestors vfmTestDefs1889
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1889_0.nsv", "result1889_1.nsv", "result1889_2.nsv", "result1889_3.nsv", "result1889_4.nsv"];
val thyn = "vfmTestDefs1889";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
