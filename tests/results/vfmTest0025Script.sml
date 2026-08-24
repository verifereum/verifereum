Theory vfmTest0025[no_sig_docs]
Ancestors vfmTestDefs0025
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0025_0.nsv", "result0025_1.nsv", "result0025_2.nsv", "result0025_3.nsv", "result0025_4.nsv", "result0025_5.nsv", "result0025_6.nsv", "result0025_7.nsv", "result0025_8.nsv", "result0025_9.nsv", "result0025_10.nsv", "result0025_11.nsv", "result0025_12.nsv", "result0025_13.nsv", "result0025_14.nsv", "result0025_15.nsv", "result0025_16.nsv", "result0025_17.nsv", "result0025_18.nsv", "result0025_19.nsv", "result0025_20.nsv", "result0025_21.nsv", "result0025_22.nsv", "result0025_23.nsv"];
val thyn = "vfmTestDefs0025";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
