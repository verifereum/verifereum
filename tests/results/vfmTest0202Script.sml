Theory vfmTest0202[no_sig_docs]
Ancestors vfmTestDefs0202
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0202_0.nsv", "result0202_1.nsv", "result0202_2.nsv", "result0202_3.nsv", "result0202_4.nsv", "result0202_5.nsv", "result0202_6.nsv", "result0202_7.nsv", "result0202_8.nsv", "result0202_9.nsv", "result0202_10.nsv", "result0202_11.nsv", "result0202_12.nsv", "result0202_13.nsv", "result0202_14.nsv", "result0202_15.nsv"];
val thyn = "vfmTestDefs0202";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
