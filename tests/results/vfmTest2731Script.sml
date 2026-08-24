Theory vfmTest2731[no_sig_docs]
Ancestors vfmTestDefs2731
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2731_0.nsv", "result2731_1.nsv", "result2731_2.nsv", "result2731_3.nsv"];
val thyn = "vfmTestDefs2731";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
