Theory vfmTest1441[no_sig_docs]
Ancestors vfmTestDefs1441
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1441_0.nsv", "result1441_1.nsv", "result1441_2.nsv", "result1441_3.nsv", "result1441_4.nsv", "result1441_5.nsv", "result1441_6.nsv", "result1441_7.nsv", "result1441_8.nsv", "result1441_9.nsv", "result1441_10.nsv", "result1441_11.nsv", "result1441_12.nsv", "result1441_13.nsv", "result1441_14.nsv", "result1441_15.nsv", "result1441_16.nsv", "result1441_17.nsv", "result1441_18.nsv", "result1441_19.nsv", "result1441_20.nsv", "result1441_21.nsv", "result1441_22.nsv", "result1441_23.nsv"];
val thyn = "vfmTestDefs1441";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
