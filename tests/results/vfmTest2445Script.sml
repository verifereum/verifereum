Theory vfmTest2445[no_sig_docs]
Ancestors vfmTestDefs2445
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2445_0.nsv", "result2445_1.nsv", "result2445_2.nsv", "result2445_3.nsv", "result2445_4.nsv", "result2445_5.nsv", "result2445_6.nsv", "result2445_7.nsv", "result2445_8.nsv", "result2445_9.nsv", "result2445_10.nsv", "result2445_11.nsv", "result2445_12.nsv", "result2445_13.nsv", "result2445_14.nsv", "result2445_15.nsv", "result2445_16.nsv", "result2445_17.nsv", "result2445_18.nsv", "result2445_19.nsv"];
val thyn = "vfmTestDefs2445";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
