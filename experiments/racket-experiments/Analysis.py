import argparse
from benchtool.Analysis import *
from benchtool.Plot import *
from functools import partial


def analyze(results: str, images: str):
    df = parse_results(results)
    print(df['time'])
    print(df['strategy'])
    if not os.path.exists(images):
        os.makedirs(images)

    # Generate task bucket charts used in Figure 3.
    for workload in ['BST']:
        times = partial(stacked_barchart_times, case=workload, df=df)
        times(
            strategies=[
                'QuickcheckBespoke',
                'RackcheckBespoke',
            ],
            colors=['#000000', '#900D0D', '#DC5F00', '#243763'],
            limits=[0.1, 1, 2, 3],
            limit_type='time',
            image_path=images,
            show=False,
        )

if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument('--data', help='path to folder for JSON data')
    p.add_argument('--figures', help='path to folder for figures')
    args = p.parse_args()

    results_path = f'{os.getcwd()}/{args.data}'
    images_path = f'{os.getcwd()}/{args.figures}'
    analyze(results_path, images_path)
