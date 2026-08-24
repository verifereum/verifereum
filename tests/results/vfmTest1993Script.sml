Theory vfmTest1993[no_sig_docs]
Ancestors vfmTestDefs1993
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1993_0.nsv", "result1993_1.nsv", "result1993_2.nsv", "result1993_3.nsv", "result1993_4.nsv", "result1993_5.nsv", "result1993_6.nsv", "result1993_7.nsv", "result1993_8.nsv", "result1993_9.nsv", "result1993_10.nsv", "result1993_11.nsv", "result1993_12.nsv", "result1993_13.nsv", "result1993_14.nsv", "result1993_15.nsv", "result1993_16.nsv", "result1993_17.nsv", "result1993_18.nsv", "result1993_19.nsv"];
val thyn = "vfmTestDefs1993";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
