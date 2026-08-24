Theory vfmTest2842[no_sig_docs]
Ancestors vfmTestDefs2842
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2842_0.nsv", "result2842_1.nsv", "result2842_2.nsv", "result2842_3.nsv"];
val thyn = "vfmTestDefs2842";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
