Theory vfmTest0191[no_sig_docs]
Ancestors vfmTestDefs0191
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0191_0.nsv", "result0191_1.nsv", "result0191_2.nsv", "result0191_3.nsv", "result0191_4.nsv", "result0191_5.nsv", "result0191_6.nsv", "result0191_7.nsv", "result0191_8.nsv", "result0191_9.nsv", "result0191_10.nsv", "result0191_11.nsv", "result0191_12.nsv", "result0191_13.nsv", "result0191_14.nsv", "result0191_15.nsv", "result0191_16.nsv", "result0191_17.nsv"];
val thyn = "vfmTestDefs0191";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
