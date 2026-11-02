Theory vfmTest0906[no_sig_docs]
Ancestors vfmTestDefs0906
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0906_0.nsv", "result0906_1.nsv", "result0906_2.nsv", "result0906_3.nsv", "result0906_4.nsv", "result0906_5.nsv", "result0906_6.nsv", "result0906_7.nsv", "result0906_8.nsv", "result0906_9.nsv", "result0906_10.nsv", "result0906_11.nsv", "result0906_12.nsv", "result0906_13.nsv", "result0906_14.nsv", "result0906_15.nsv", "result0906_16.nsv", "result0906_17.nsv", "result0906_18.nsv", "result0906_19.nsv", "result0906_20.nsv", "result0906_21.nsv", "result0906_22.nsv", "result0906_23.nsv"];
val thyn = "vfmTestDefs0906";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
