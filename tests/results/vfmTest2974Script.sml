Theory vfmTest2974[no_sig_docs]
Ancestors vfmTestDefs2974
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2974_0.nsv", "result2974_1.nsv", "result2974_2.nsv", "result2974_3.nsv", "result2974_4.nsv", "result2974_5.nsv", "result2974_6.nsv", "result2974_7.nsv", "result2974_8.nsv", "result2974_9.nsv", "result2974_10.nsv", "result2974_11.nsv", "result2974_12.nsv", "result2974_13.nsv", "result2974_14.nsv", "result2974_15.nsv", "result2974_16.nsv"];
val thyn = "vfmTestDefs2974";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
