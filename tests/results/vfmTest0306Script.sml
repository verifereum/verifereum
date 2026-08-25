Theory vfmTest0306[no_sig_docs]
Ancestors vfmTestDefs0306
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0306_0.nsv", "result0306_1.nsv", "result0306_2.nsv", "result0306_3.nsv", "result0306_4.nsv", "result0306_5.nsv", "result0306_6.nsv", "result0306_7.nsv", "result0306_8.nsv", "result0306_9.nsv", "result0306_10.nsv", "result0306_11.nsv", "result0306_12.nsv", "result0306_13.nsv", "result0306_14.nsv", "result0306_15.nsv", "result0306_16.nsv", "result0306_17.nsv"];
val thyn = "vfmTestDefs0306";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
