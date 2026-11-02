Theory vfmTest0889[no_sig_docs]
Ancestors vfmTestDefs0889
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0889_0.nsv", "result0889_1.nsv", "result0889_2.nsv", "result0889_3.nsv", "result0889_4.nsv", "result0889_5.nsv", "result0889_6.nsv", "result0889_7.nsv", "result0889_8.nsv", "result0889_9.nsv", "result0889_10.nsv", "result0889_11.nsv", "result0889_12.nsv", "result0889_13.nsv", "result0889_14.nsv", "result0889_15.nsv", "result0889_16.nsv", "result0889_17.nsv", "result0889_18.nsv", "result0889_19.nsv", "result0889_20.nsv", "result0889_21.nsv", "result0889_22.nsv", "result0889_23.nsv", "result0889_24.nsv", "result0889_25.nsv", "result0889_26.nsv", "result0889_27.nsv", "result0889_28.nsv"];
val thyn = "vfmTestDefs0889";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
