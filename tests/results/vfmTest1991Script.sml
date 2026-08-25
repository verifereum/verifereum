Theory vfmTest1991[no_sig_docs]
Ancestors vfmTestDefs1991
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1991_0.nsv", "result1991_1.nsv", "result1991_2.nsv", "result1991_3.nsv", "result1991_4.nsv", "result1991_5.nsv", "result1991_6.nsv", "result1991_7.nsv", "result1991_8.nsv", "result1991_9.nsv", "result1991_10.nsv", "result1991_11.nsv", "result1991_12.nsv", "result1991_13.nsv", "result1991_14.nsv", "result1991_15.nsv", "result1991_16.nsv", "result1991_17.nsv", "result1991_18.nsv", "result1991_19.nsv"];
val thyn = "vfmTestDefs1991";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
