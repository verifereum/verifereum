Theory vfmTest1770[no_sig_docs]
Ancestors vfmTestDefs1770
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1770_0.nsv", "result1770_1.nsv", "result1770_2.nsv", "result1770_3.nsv", "result1770_4.nsv", "result1770_5.nsv", "result1770_6.nsv", "result1770_7.nsv", "result1770_8.nsv", "result1770_9.nsv", "result1770_10.nsv", "result1770_11.nsv", "result1770_12.nsv", "result1770_13.nsv", "result1770_14.nsv", "result1770_15.nsv"];
val thyn = "vfmTestDefs1770";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
