Theory vfmTest1662[no_sig_docs]
Ancestors vfmTestDefs1662
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1662_0.nsv", "result1662_1.nsv", "result1662_2.nsv", "result1662_3.nsv", "result1662_4.nsv", "result1662_5.nsv", "result1662_6.nsv", "result1662_7.nsv", "result1662_8.nsv", "result1662_9.nsv", "result1662_10.nsv", "result1662_11.nsv", "result1662_12.nsv", "result1662_13.nsv", "result1662_14.nsv", "result1662_15.nsv"];
val thyn = "vfmTestDefs1662";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
