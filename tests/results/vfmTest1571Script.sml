Theory vfmTest1571[no_sig_docs]
Ancestors vfmTestDefs1571
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1571_0.nsv", "result1571_1.nsv", "result1571_2.nsv", "result1571_3.nsv", "result1571_4.nsv", "result1571_5.nsv", "result1571_6.nsv", "result1571_7.nsv", "result1571_8.nsv", "result1571_9.nsv", "result1571_10.nsv", "result1571_11.nsv", "result1571_12.nsv", "result1571_13.nsv", "result1571_14.nsv", "result1571_15.nsv", "result1571_16.nsv", "result1571_17.nsv", "result1571_18.nsv", "result1571_19.nsv"];
val thyn = "vfmTestDefs1571";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
