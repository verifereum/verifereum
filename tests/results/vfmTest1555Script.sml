Theory vfmTest1555[no_sig_docs]
Ancestors vfmTestDefs1555
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1555_0.nsv", "result1555_1.nsv", "result1555_2.nsv", "result1555_3.nsv", "result1555_4.nsv", "result1555_5.nsv", "result1555_6.nsv", "result1555_7.nsv", "result1555_8.nsv", "result1555_9.nsv", "result1555_10.nsv", "result1555_11.nsv", "result1555_12.nsv", "result1555_13.nsv", "result1555_14.nsv", "result1555_15.nsv", "result1555_16.nsv", "result1555_17.nsv", "result1555_18.nsv", "result1555_19.nsv"];
val thyn = "vfmTestDefs1555";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
