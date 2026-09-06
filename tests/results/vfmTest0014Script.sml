Theory vfmTest0014[no_sig_docs]
Ancestors vfmTestDefs0014
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0014_0.nsv", "result0014_1.nsv", "result0014_2.nsv", "result0014_3.nsv", "result0014_4.nsv", "result0014_5.nsv", "result0014_6.nsv", "result0014_7.nsv", "result0014_8.nsv", "result0014_9.nsv", "result0014_10.nsv", "result0014_11.nsv", "result0014_12.nsv", "result0014_13.nsv", "result0014_14.nsv", "result0014_15.nsv", "result0014_16.nsv", "result0014_17.nsv", "result0014_18.nsv", "result0014_19.nsv", "result0014_20.nsv", "result0014_21.nsv", "result0014_22.nsv", "result0014_23.nsv", "result0014_24.nsv", "result0014_25.nsv", "result0014_26.nsv", "result0014_27.nsv", "result0014_28.nsv", "result0014_29.nsv"];
val thyn = "vfmTestDefs0014";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
