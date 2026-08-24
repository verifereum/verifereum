Theory vfmTest0857[no_sig_docs]
Ancestors vfmTestDefs0857
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0857_0.nsv", "result0857_1.nsv", "result0857_2.nsv", "result0857_3.nsv", "result0857_4.nsv", "result0857_5.nsv", "result0857_6.nsv", "result0857_7.nsv", "result0857_8.nsv", "result0857_9.nsv", "result0857_10.nsv", "result0857_11.nsv", "result0857_12.nsv", "result0857_13.nsv", "result0857_14.nsv", "result0857_15.nsv", "result0857_16.nsv", "result0857_17.nsv", "result0857_18.nsv", "result0857_19.nsv", "result0857_20.nsv", "result0857_21.nsv", "result0857_22.nsv", "result0857_23.nsv"];
val thyn = "vfmTestDefs0857";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
