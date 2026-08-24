Theory vfmTest2778[no_sig_docs]
Ancestors vfmTestDefs2778
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2778_0.nsv", "result2778_1.nsv", "result2778_2.nsv", "result2778_3.nsv"];
val thyn = "vfmTestDefs2778";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
