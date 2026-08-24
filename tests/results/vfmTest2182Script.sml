Theory vfmTest2182[no_sig_docs]
Ancestors vfmTestDefs2182
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2182_0.nsv", "result2182_1.nsv", "result2182_2.nsv", "result2182_3.nsv", "result2182_4.nsv", "result2182_5.nsv", "result2182_6.nsv", "result2182_7.nsv", "result2182_8.nsv", "result2182_9.nsv"];
val thyn = "vfmTestDefs2182";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
