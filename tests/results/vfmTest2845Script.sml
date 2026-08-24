Theory vfmTest2845[no_sig_docs]
Ancestors vfmTestDefs2845
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2845_0.nsv", "result2845_1.nsv", "result2845_2.nsv", "result2845_3.nsv"];
val thyn = "vfmTestDefs2845";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
