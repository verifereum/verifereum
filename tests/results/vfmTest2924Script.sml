Theory vfmTest2924[no_sig_docs]
Ancestors vfmTestDefs2924
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2924_0.nsv", "result2924_1.nsv", "result2924_2.nsv", "result2924_3.nsv", "result2924_4.nsv", "result2924_5.nsv", "result2924_6.nsv", "result2924_7.nsv", "result2924_8.nsv", "result2924_9.nsv", "result2924_10.nsv", "result2924_11.nsv", "result2924_12.nsv", "result2924_13.nsv", "result2924_14.nsv", "result2924_15.nsv"];
val thyn = "vfmTestDefs2924";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
