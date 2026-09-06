Theory vfmTest0184[no_sig_docs]
Ancestors vfmTestDefs0184
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0184_0.nsv", "result0184_1.nsv", "result0184_2.nsv", "result0184_3.nsv", "result0184_4.nsv", "result0184_5.nsv", "result0184_6.nsv", "result0184_7.nsv", "result0184_8.nsv", "result0184_9.nsv", "result0184_10.nsv", "result0184_11.nsv", "result0184_12.nsv", "result0184_13.nsv", "result0184_14.nsv", "result0184_15.nsv", "result0184_16.nsv", "result0184_17.nsv"];
val thyn = "vfmTestDefs0184";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
