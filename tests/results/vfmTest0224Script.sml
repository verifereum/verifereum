Theory vfmTest0224[no_sig_docs]
Ancestors vfmTestDefs0224
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0224_0.nsv", "result0224_1.nsv", "result0224_2.nsv", "result0224_3.nsv", "result0224_4.nsv", "result0224_5.nsv", "result0224_6.nsv", "result0224_7.nsv", "result0224_8.nsv", "result0224_9.nsv", "result0224_10.nsv", "result0224_11.nsv", "result0224_12.nsv", "result0224_13.nsv", "result0224_14.nsv", "result0224_15.nsv", "result0224_16.nsv", "result0224_17.nsv", "result0224_18.nsv", "result0224_19.nsv", "result0224_20.nsv", "result0224_21.nsv"];
val thyn = "vfmTestDefs0224";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
