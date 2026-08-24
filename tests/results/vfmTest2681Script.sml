Theory vfmTest2681[no_sig_docs]
Ancestors vfmTestDefs2681
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2681_0.nsv", "result2681_1.nsv", "result2681_2.nsv", "result2681_3.nsv"];
val thyn = "vfmTestDefs2681";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
