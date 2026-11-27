Theory vfmTest0434[no_sig_docs]
Ancestors vfmTestDefs0434
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0434_0.nsv", "result0434_1.nsv", "result0434_2.nsv", "result0434_3.nsv", "result0434_4.nsv", "result0434_5.nsv", "result0434_6.nsv", "result0434_7.nsv", "result0434_8.nsv", "result0434_9.nsv", "result0434_10.nsv", "result0434_11.nsv", "result0434_12.nsv", "result0434_13.nsv", "result0434_14.nsv", "result0434_15.nsv", "result0434_16.nsv", "result0434_17.nsv", "result0434_18.nsv", "result0434_19.nsv", "result0434_20.nsv", "result0434_21.nsv", "result0434_22.nsv", "result0434_23.nsv", "result0434_24.nsv", "result0434_25.nsv", "result0434_26.nsv"];
val thyn = "vfmTestDefs0434";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
